from mininet.topo import Topo
from mininet.net import Mininet
from mininet.node import RemoteController, OVSKernelSwitch
from mininet.link import TCLink, TCIntf
from mininet.util import dumpNodeConnections,dumpNetConnections, dumpPorts
from mininet.cli import CLI
from mininet.log import setLogLevel

from ryu.lib import hub
from sys import argv
import argparse

#Link parameter
linkopts1 = dict(bw=1,  delay='1ms') #Host link
#linkopts2 = [dict(loss=2, bw=1000, delay='3ms'),dict(bw=1000, delay='3ms'),dict(loss=5, bw=1000, delay='3ms')] #Switch Link
linkopts2 = dict( bw=1, delay='2ms') #Switch Link, link loss=10%


##########################################################################################
#Custom Topology
class MyTopo(Topo):
    def __init__(self, noOFS=8, noHost=1):
        Topo.__init__(self)

        noOFS = noOFS
        noHost= noHost
        Host = []
        OFS  = []

        #Add Host to topology
        for i in range(noOFS*noHost):
            Host.append(self.addHost("h{}".format(i+1), ip="10.0.{}.{}".format(i+1,i+1)))
            
        Host.append(self.addHost("h{}".format(8),ip="10.0.8.{}".format(8)))
        Host.append(self.addHost("h{}".format(9),ip="10.0.1.{}".format(9)))
        Host.append(self.addHost("h{}".format(10),ip="10.0.1.{}".format(10)))
        Host.append(self.addHost("h{}".format(11),ip="10.0.1.{}".format(11)))
        Host.append(self.addHost("h{}".format(12),ip="10.0.1.{}".format(12)))
        for host in Host:
            print(host)
        #Add Switch to topology
        for i in range(noOFS):
            OFS.append(self.addSwitch("s{}".format(i+1)))

        #Link Host to Switch
        for i in range(noOFS):
            for j in range(noHost):
                if j < 9:
                    self.addLink(Host[i*noHost+j],OFS[i],**linkopts1)
        
        self.addLink(Host[9],OFS[0],**linkopts1)
        self.addLink(Host[10],OFS[0],**linkopts1)
        self.addLink(Host[11],OFS[0],**linkopts1)
        self.addLink(Host[12],OFS[0],**linkopts1)

        self.addLink(OFS[0], OFS[1],**linkopts2)
        self.addLink(OFS[0],OFS[3],**linkopts2)
        self.addLink(OFS[0],OFS[5],**linkopts2)

        self.addLink(OFS[1],OFS[2],**linkopts2)
        self.addLink(OFS[3],OFS[4],**linkopts2)
        self.addLink(OFS[5],OFS[6],**linkopts2)


        self.addLink(OFS[6],OFS[7],**linkopts2)
        self.addLink(OFS[4],OFS[7],**linkopts2)
        self.addLink(OFS[2],OFS[7],**linkopts2)
##########################################################################################
#Main function:
def main(*args):
    parser = argparse.ArgumentParser()
    parser.add_argument('--NumOFS',  type=int, action="store", default=8)
    parser.add_argument('--NumHost', type=int, action="store", default=1)
    args = parser.parse_args()

    NumOFS = args.NumOFS
    NumHost= args.NumHost

    mytopo = MyTopo(NumOFS,NumHost)
    net  = Mininet(topo=mytopo, switch=OVSKernelSwitch, 
                   controller=RemoteController("c0", ip="127.0.0.1"), 
                   autoSetMacs=True, link=TCLink)
    
    print("---------------------- NETS ------------------------")
    dumpNetConnections(net)
    print("----------------------------------------------------\n")

    #Run default command from hosts. E.g., Disable IPv6:
    for h in net.hosts:
        h.cmd("sysctl -w net.ipv6.conf.all.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv6.conf.default.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv6.conf.lo.disable_ipv6=1")

    #Start simulation --------------------------
    net.start()

    #Ex: h1 ping h4
    h1 = net.getNodeByName("h1")
    CLI(net)
    #Stop simulation ----------------------------
    net.stop()


##########################################################################################
#Default run simulation
if __name__ == "__main__":
    setLogLevel("info")
    main()
