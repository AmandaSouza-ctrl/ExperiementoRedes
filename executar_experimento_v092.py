#!/usr/bin/python3
# -*- coding: utf-8 -*-

"""
Experimento SDN/Mininet – versão 92
────────────────────────────────────────────────────────────────────────
• Corrige exibição do “Mapa de larguras”  →  link.bw agora é atribuído
  logo após a criação do Link.
• Adiciona linha-cabeçalho com legendas antes de cada ciclo.
• Comentários pedagógicos em todas as partes críticas (↑ avaliar fonte
  dos dados de telemetria).
"""

import os, sys, time, csv, re, argparse, logging, random, shutil, subprocess
import itertools, unicodedata
from pathlib import Path
from itertools import permutations
import networkx as nx
from mininet.net  import Mininet
from mininet.node import OVSKernelSwitch
from mininet.link import TCLink
from mininet.clean import cleanup
from mininet.log  import setLogLevel

# ────────── CONSTANTES ────────────────────────────────────────────────
PING_CNT, PING_INT = 5, 0.2              # pacotes & intervalo ping
IPERF_TIME         = 2                   # duração iperf UDP [s]
IPERF_PORT         = 5201
STAMP              = time.strftime("%Y%m%d_%H%M%S")

# ────────── UTIL de arquivo único + chmod 777/666 ─────────────────────
def unique_file(folder: str, stem: str, ext: str) -> Path:
    Path(folder).mkdir(parents=True, exist_ok=True)
    os.chmod(folder, 0o777)
    p = Path(folder)/f"{stem}.{ext}"
    if not p.exists():
        p.touch(); os.chmod(p,0o666); return p
    for i in itertools.count(1):
        q = Path(folder)/f"{stem}_{i:03d}.{ext}"
        if not q.exists():
            q.touch(); os.chmod(q,0o666); return q

LOG_FILE = unique_file("logs",     f"{STAMP}_log",        "txt")
CSV_FILE = unique_file("database", f"{STAMP}_telemetria", "csv")

# ────────── LOG ascii-safe ────────────────────────────────────────────
class AsciiFmt(logging.Formatter):
    def format(self, rec):
        return unicodedata.normalize("NFKD",
               super().format(rec)).encode("ascii","ignore").decode()

def mk_logger(clean=False):
    lg=logging.getLogger("exp"); lg.handlers.clear(); lg.setLevel(logging.DEBUG)
    fh=logging.FileHandler(LOG_FILE,"w",encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s  %(levelname)s  %(message)s"))
    fh.setLevel(logging.DEBUG); lg.addHandler(fh)
    sh=logging.StreamHandler(sys.stdout)
    sh.setFormatter(AsciiFmt("%(levelname)s %(message)s"))
    sh.setLevel(logging.INFO if not clean else logging.WARNING)
    lg.addHandler(sh)
    return lg

def banner(lg, txt): lg.info("="*75); lg.info(txt.center(75)); lg.info("="*75)

# ────────── FLOWS & MEDIÇÕES ──────────────────────────────────────────
def get_port(sw, peer):
    """Retorna nº porta de sw conectada ao peer."""
    link = sw.connectionsTo(peer)
    if not link: return None
    return int(link[0][0].name.split("-eth")[1])

def install_flows(net, path, hsrc, hdst):
    """Instala regras OpenFlow estáticas caminho-a-caminho."""
    for sw in net.switches: sw.cmd("ovs-ofctl del-flows", sw)
    for i, swname in enumerate([n for n in path if n.startswith("s")]):
        sw   = net.get(swname)
        pin  = get_port(sw, net.get(path[i]))
        pout = get_port(sw, net.get(path[i+2]))
        if None in (pin,pout): return False
        # ARP bidirecional
        for a,b in ((pin,pout),(pout,pin)):
            sw.cmd(f"ovs-ofctl add-flow {sw} priority=50,arp,in_port={a},actions=output:{b}")
        # ICMP & IP bidirecional
        for pr,proto in ((10,"ip"),(100,"icmp")):
            sw.cmd(f"ovs-ofctl add-flow {sw} priority={pr},{proto},in_port={pin},"
                   f"nw_src={hsrc.IP()},nw_dst={hdst.IP()},actions=output:{pout}")
            sw.cmd(f"ovs-ofctl add-flow {sw} priority={pr},{proto},in_port={pout},"
                   f"nw_src={hdst.IP()},nw_dst={hsrc.IP()},actions=output:{pin}")
    return True

def parse_ping(out):
    """Extrai RTT médio (ms) da saída do ping."""
    m=re.search(r"min/avg/max/[^\s=]* = [\d\.]+/([\d\.]+)/",out)
    return float(m.group(1)) if m else "FAIL"

def iperf_bw(src, dst, mbit, lg):
    """Executa iperf3 UDP → retorna BW em Mb/s (FLOAT) ou 'FAIL'/'-'."""
    if mbit==0 or not shutil.which("iperf3"): return "-"
    # servidor (-1 = encerra apos 1 cliente)
    srv = dst.popen(["iperf3","-s","-1","-p",str(IPERF_PORT)],
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    time.sleep(0.25)
    out = src.cmd(f"iperf3 -u -b {mbit}M -t {IPERF_TIME} -p {IPERF_PORT} "
                  f"-c {dst.IP()} -f m")
    srv_out,_ = srv.communicate()
    lg.debug("[IPERF RAW]\n--- server ---\n"+srv_out+"\n--- client ---\n"+out)
    m=re.search(r"([\d\.]+)\s+Mbits/sec.*receiver",out,re.S|re.I) \
      or re.search(r"([\d\.]+)\s+Mbits/sec",srv_out)
    return float(m.group(1)) if m else "FAIL"

# ────────── MAPA DE BW ────────────────────────────────────────────────
def show_bw_map(net, lg):
    lg.info("Mapa de larguras (Mb/s):")
    for l in net.links:
        bw = getattr(l,'bw','-')
        n1 = l.intf1.node.name
        n2 = l.intf2.node.name
        lg.info(f"  [LINK] {n1:<3}-{n2:<3} {bw if bw=='-' else int(bw):>6}")

# ────────── EXECUÇÃO PRINCIPAL ────────────────────────────────────────
def run(cfg):
    lg = mk_logger(cfg.clean)
    banner(lg,"INICIO EXPERIMENTO v92")
    lg.info("Parametros em uso:")
    for k,v in vars(cfg).items(): lg.info(f"  {k:<6}= {v}")

    # ----- carrega topologia textual -----
    links=[tuple(map(int,l.split())) for l in open(cfg.topo) if l.strip()]
    ids  =sorted(set(sum(links,())))
    G=nx.Graph()
    for u,v in links: G.add_edge(f"s{u}",f"s{v}")
    for i in ids:     G.add_edge(f"h{i}",f"s{i}")

    # ----- todos os caminhos -----
    paths=[]
    for a,b in permutations(ids,2):
        p=list(nx.all_simple_paths(G,f"h{a}",f"h{b}"))
        if cfg.mini: p=sorted(p,key=len)[:cfg.mini]
        paths.extend([(f"h{a}",f"h{b}",pp) for pp in p])

    # ----- rede Mininet -----
    cleanup()
    net=Mininet(controller=None,switch=OVSKernelSwitch,link=TCLink,
                autoSetMacs=True)
    for i in ids:
        bw = cfg.rand() if cfg.rand else cfg.bw
        net.addHost(f"h{i}",ip=f"10.0.0.{i}/24")
        sw = net.addSwitch(f"s{i}")
        lk = net.addLink(f"h{i}",sw,bw=bw)
        lk.bw = bw if bw else "-"          # armazena para exibir depois
    for u,v in links:
        bw = cfg.rand() if cfg.rand else cfg.bw
        lk = net.addLink(f"s{u}",f"s{v}",bw=bw)
        lk.bw = bw if bw else "-"
    net.start(); lg.info("Rede iniciada, pausa 2 s"); time.sleep(2)
    show_bw_map(net,lg)

    # cabeçalho CSV
    with open(CSV_FILE,"w",newline="") as f:
        csv.writer(f).writerow(["cycle","idx","src","dst","hops",
                                "path","rtt_ms","bw_mbps","timestamp"])

    # ----- ciclo -----
    def ciclo(cx):
        lg.info(f"CICLO {cx}")
        lg.info(f"{'ID':>5} | {'CAMINHO':<55} | {'RTT ms':>9} | {'BW Mb/s':>10}")
        lg.info("-"*86)
        for idx,(src,dst,path) in enumerate(paths,1):
            hops=len(path)-1
            ok=install_flows(net,path,net.get(src),net.get(dst))
            rtt=parse_ping(net.get(src).cmd(
                f"ping -c {PING_CNT} -i {PING_INT} -W 2 {net.get(dst).IP()}")) if ok else "FAIL"
            bw = iperf_bw(net.get(src),net.get(dst),cfg.iperf,lg) if ok else "FAIL"
            lg.info(f"{idx:02d}/{len(paths):02d} | "
                    f"{'>'.join(path):<55} | "
                    f"{rtt if rtt=='FAIL' else f'{rtt:9.3f}'} | "
                    f"{bw  if bw =='FAIL' else f'{bw:10.3f}'}")
            with open(CSV_FILE,"a",newline="") as f:
                csv.writer(f).writerow([cx,idx,src,dst,hops,"->".join(path),
                                        rtt,bw,time.time()])
            time.sleep(cfg.warm)

    start=time.time(); cycles=0
    try:
        if cfg.time==0: cycles=1; ciclo(1)
        else:
            end=start+cfg.time*60
            while time.time()<end:
                cycles+=1; ciclo(cycles)
    except KeyboardInterrupt:
        lg.warning("Interrompido")
    finally:
        lg.info("Parando rede…"); net.stop()

# ────────── ARGPARSE ──────────────────────────────────────────────────
p=argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter,
    description="Medidor de latência + bw SDN/Mininet (v92)")
p.add_argument("-topo", required=True)
p.add_argument("-time", type=int, default=0)
p.add_argument("-mini", type=int)
p.add_argument("-warm", type=float, default=0.2)
p.add_argument("-iperf", type=int, default=0, metavar="MBPS")
p.add_argument("-clean", action="store_true")
p.add_argument("-graph", action="store_true")

grp=p.add_mutually_exclusive_group()
grp.add_argument("-bw", type=float, metavar="Gbps")
grp.add_argument("-bwRand", type=str, metavar="LO-HI")

cfg=p.parse_args()
# se aleatório, gera função que retorna Mb/s
if cfg.bwRand:
    lo,hi=map(float,cfg.bwRand.split("-"))
    cfg.rand=lambda: random.uniform(lo*1000, hi*1000)
    cfg.bw=None
else:
    cfg.rand=None
run(cfg)
