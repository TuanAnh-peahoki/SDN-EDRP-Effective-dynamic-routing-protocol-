import time
from scapy.all import *
import time
import sys
import string, random

letters = string.ascii_lowercase
result_str = ''.join(random.choice(letters) for i in range(83))
pkt_start = IP(dst="10.0.8.8")/ICMP()/ result_str
while 1:
    # Send 1 Probe packet. It will come to OFC via PacketIn message.
    # OFC will not forward this packet. OFC applies the flow entries for the probe packets
    #print("\nSend 1 probe packet and wait 1 second")
    
    # Send 10,000 probe packets in 1 second
    #print("Send 1,0000 probe packets in 1 second")
    send( pkt_start,count = 100000, verbose=0)#,inter=1.0/200000
    time.sleep(1)
    print("Start")
