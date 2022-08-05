from codecs import ignore_errors
from distutils.command.install_scripts import install_scripts
from re import L, S
from tokenize import Ignore
from typing import Any
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import MAIN_DISPATCHER, CONFIG_DISPATCHER, DEAD_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3, ether, inet
from ryu.lib.packet import packet ,ether_types, ethernet, arp, lldp, icmpv6 , udp, ipv4, in_proto, tcp 
from ryu.lib import hub
from ryu.topology import event
from ryu.topology.api import get_switch, get_link
import ryu.app.ofctl.api as ofctl_api
import itertools
import numpy as np

import operator
import random
import string
from collections import OrderedDict
import time
import sys
from decimal import Decimal as D
from operator import attrgetter
import datetime
import copy
import math

flow_idle_timeout=10 #idle timout for the flow

REFERENCE_BW = 10000000
MAX_PATH = 3

class Report(app_manager.RyuApp):
    OFP_VERSIONS= [ofproto_v1_3.OFP_VERSION]
    """
    
    
    Dictionary and Array store  
    
    
    """
    def __init__(self,*args,**kwargs):
        super(Report,self).__init__(*args,**kwargs)
        self.MAC_table  = {} # Create blank MAC table 
        self.ARP_table  =   {} # Create blank ARP table

        
        self.datapaths  =   {} # Create the datapths table

        self.Topology_db = {} # Create the topology database
        self.network_changed_thread=None
        self.port_switch={}
        self.port_host={}
        self.Switch_switch_db = {} # Create Switch Link
            
        self.link_connection_switch = {}
        self.switch_port_connect= []
        self.port_host_connect=[]
        self.learn_dict={}
        self.switch_drop = {}
        ###################### ARP flag #####################################################
        self.exist = False
        ###################### Store bandwidth for each link ################################
        self.bandwidth = {}
        self.link_capacity = {}
        self.data_rate = []
        self.data_rate_2 = {}
        self.count_link_capacity = 0
        self.save_path_with_port = []
        self.count_for_flow = 0
        self.link_ultility = []
        self.monitor_thread = hub.spawn(self.monitor)
        self.relocate_thread = hub.spawn(self.relocate_flow_periodically)
        self.the_first_setup_data_rate = False
        self.after_the_calculate_date_rate =  False
        self.First = True
        self.data_rate_3 = {}
        self.flow_priority_2_exist = False
        ###################### ECMP -load balancing routing  ################################
        self.equal_cost = False
        self.equal_cost_reserve = False
        self.optimal_path = {}
        self.group = {}
        self.flow_recent_exist = []
        self.flag_flow_already_used = False
        self.flag_different = False
        self.the_first_flow_stat_request = False
        self.the_second_flow_stat_request = False
        self.flag_ready_to_receive = False
        self.count_flow = 0
        self.ready_to_send = False
        self.flow_recent_exist_compare = []
        self.ready = False
        self.have_replica_flow = False
    ##############################################################
    # Add action for "missing flow"
    #
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures,CONFIG_DISPATCHER)
    def action_for_missing_flow(self, ev):
        msg         =     ev.msg
        datapath          =     msg.datapath
        ofproto     =     datapath.ofproto
        ofp_parser  =     datapath.ofproto_parser
        match       =     ofp_parser.OFPMatch()

        
        actions         =    [ofp_parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,ofproto.OFPCML_NO_BUFFER)]
        instructions    = [ofp_parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
        self.flow_add(datapath,0,0,None,instructions,0,0,0,0)

    ##############################################################  
    # Store and Map "Datapath" and "Datapath ID"
    #
    @set_ev_cls(ofp_event.EventOFPStateChange, [MAIN_DISPATCHER, DEAD_DISPATCHER])
    def StateChange(self, ev):
        dp   = ev.datapath
        dpid = dp.id
        
        if ev.state == MAIN_DISPATCHER:
            self.datapaths.setdefault(dpid,dp)
            
        if ev.state == DEAD_DISPATCHER:
            if (self.datapaths):
                self.datapaths.pop(dpid)

    ##############################################################
    # Handle PACKET-IN message
    #
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER) 
    def packet_in_handler(self,ev):
        msg =   ev.msg
        dp  =   msg.datapath
        ofp =   dp.ofproto
        ofp_parser  =   dp.ofproto_parser

        buffer_id = msg.buffer_id
        pkt =   packet.Packet(msg.data) #Get Packet
        etherh  =   pkt.get_protocol(ethernet.ethernet)     # Ethernet Header         
        smac    =   etherh.src                              # Source MAC address
        dmac    =   etherh.dst                              # Destination MAC address
        pin     =   msg.match['in_port']                    # port in
        pout    =   0                                       # port out doesn't know at first
        dpid    =   dp.id                                   # Switch ID
        
        #Ignore LLDP, ICMPv6 packets
        if pkt.get_protocol(lldp.lldp) or pkt.get_protocol(icmpv6.icmpv6):
            return

        #print("\n\n\n OFC receives Packet-In message from Datapath ID of {} ------ Log at:{}".format(dpid,datetime.datetime.now))

        #Learn source MAC address and port
        # *** Only at the edge OFS
        self.MAC_table.setdefault(dpid,{})
        if(self.MAC_table[dpid].get(smac) !=  pin):
            self.MAC_table[dpid][smac]    =   pin
            print("\n   - Updates MAC table: MAC={} <-> Port{}".format(smac,pin))
            # print(self.MAC_table)
        #Handle the ARP packet
        # 1. Learn the MAC address <--> IPv4 Address (ARP table)
        # 2. If Controller's ARP table already has the Destination MAC address and Destination IPv4 address
        # OFC creates the ARP reply and forward to the End Host via the Packetout message
        self.arp_handling(dpid, pin, smac, dmac, ofp_parser, dp, ofp, etherh, pkt, pout, buffer_id)
        #self.UDP_handling(dpid, pin, smac, dmac, ofp_parser, dp, ofp, etherh, pkt, pout, buffer_id, msg.data)
    
    """

    
    ARP handling
    
    
    """


    ################################################################################################################################################################################################
    # Handle ARP request protocol
    #
    def arp_handling(self,in_dpid,in_pin,in_smac,in_dmac,in_ofp_parser,in_dp,in_ofp,in_etherh,in_pkt,out_port,buffer):
        arp_pkt=in_pkt.get_protocol(arp.arp)
        if arp_pkt:
            print("")
            _sip = arp_pkt.src_ip
            _dip = arp_pkt.dst_ip
            if arp_pkt.opcode == arp.ARP_REQUEST:
                
                print ("\n   - Receives a ARP request packet from host {} ({}) aksing the MAC of {}". format(_sip,in_smac,_dip))
                # Update ARP table
                self.ARP_table.setdefault(in_dpid,{})
                if len(self.ARP_table.values()) == 1:
                    # print(self.ARP_table)
                    self.ARP_table[in_dpid][in_smac]    =   _sip
                    print("\n      + Update ARP table: MAC={} <--> IPv4={}".format(in_smac,_sip))

                    print("\n      + {} is not in ARP table".format(_dip))
                    self.ARP_MAC_not_in_table(dpid=in_dpid,smac=in_smac,sip=_sip,dip=_dip,ipin=in_pin,buffer_id=buffer)
                else:
                    #print(self.ARP_table)
                    for sw in list(self.ARP_table.keys()):
                        if int(_dip.split('.')[2]) == sw:
                            for mac, ip in list(self.ARP_table[sw].items()):
                                if _dip == ip:
                                    self.exist = True
                                    break
                                else:
                                    self.exist= False
                        else:
                            continue
                    if self.exist:        
                        self.ARP_table[in_dpid][in_smac] = _sip
                        print("\n      + Update ARP table: MAC={} <--> IPv4={}".format(in_smac,_sip))
                        # print("\n + The ARP table after update: {}".format(self.ARP_table))
                        ################################################################################################################################################################################################
                        # Send the ARP reply packet when the destination IP address already in ARP table
                        #
                        for _dpid in self.ARP_table.keys():
                            if _dip in self.ARP_table[_dpid].values():
                                for _dmac in self.ARP_table[_dpid].keys():
                                    if self.ARP_table[_dpid][_dmac] ==   _dip:
                                        print("\n   +Creates and returns the ARP reply packet1: IPv4={} <--> MAC={}".format(_dip,_dmac))
                                        have_arp_info=True

                                        e   =   ethernet.ethernet(dst=in_smac,src=_dmac,ethertype=ether.ETH_TYPE_ARP)
                                        a   =   arp.arp ( hwtype=1,proto=0x0800,hlen=6,plen=4,opcode=2,
                                                                        
                                                                    src_mac=_dmac, src_ip=_dip,
                                                                    dst_mac=in_smac, dst_ip=_sip)
                                                                    
                                                                                                    
                                        p=packet.Packet()
                                        p.add_protocol(e)
                                        p.add_protocol(a)
                                        p.serialize()
                                                    
                                        actions = [in_ofp_parser.OFPActionOutput(in_pin)]
                                        self.send_packet(in_dp,in_ofp.OFP_NO_BUFFER,in_ofp.OFPP_CONTROLLER,actions,p.data)
                                        dpid_dest = self.Get_dst_dpid(_dmac)
                                        path_route=[]
                                        path_route = self.FindRoute(in_dpid,dpid_dest,self.MAC_table[in_dpid][in_smac],self.MAC_table[dpid_dest][_dmac],in_smac,_dmac)
                                        print("\n------------------------------------- Route -------------------------------------")
                                        print("\n Optimal path: {}".format(path_route))
                                        print("\n   - Start adding flow entries to all OFS on the path route:") 
                                        for i in range(len(path_route)):
                                            _dp         = self.datapaths[list(path_route.keys())[i]]
                                            _ofp        = _dp.ofproto
                                            _ofp_parser = _dp.ofproto_parser

                                            _pin = path_route[_dp.id][0]
                                            _pout = path_route[_dp.id][1]
                                                # Prepare and send Flow Mod ( add new entry to the OFS)
                                                #Forward
                                            _actions = [_ofp_parser.OFPActionOutput(_pout)]
                                            _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
                                            _match   = _ofp_parser.OFPMatch(eth_dst=in_smac, in_port=_pin)
                                            self.flow_add(_dp, flow_idle_timeout, 2, _match, _inst,in_smac,0,_pout,_dp.id)
                                                        
                                                # Backward
                                            _actions = [_ofp_parser.OFPActionOutput(_pin)]
                                            _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
                                            _match   = _ofp_parser.OFPMatch(eth_dst=_dmac, in_port=_pout)
                                            self.flow_add(_dp,flow_idle_timeout, 2, _match, _inst,_dmac,0,_pin,_dp.id)
                        
                                        break
                    else:        
                        self.ARP_table[in_dpid][in_smac]    =   _sip
                        print("      + Update ARP table: MAC={} <--> IPv4={}".format(in_smac,_sip))

                        print("      + {} is not in ARP table".format(_dip))
                        self.ARP_MAC_not_in_table(dpid=in_dpid,smac=in_smac,sip=_sip,dip=_dip,ipin=in_pin,buffer_id=buffer)          
    ################################################################################################################################################################################################
    # Handle ARP reply message
    #        
            if arp_pkt.opcode == arp.ARP_REPLY:
                print ("   - Receives a ARP reply packet from host {} ({}) answering the MAC of {}". format(_sip,in_smac,_dip))
                # Update ARP table
                self.ARP_table.setdefault(in_dpid,{})
                if (self.ARP_table[in_dpid].get(in_smac)    !=  _sip):
                    self.ARP_table[in_dpid][in_smac]    =   _sip
                    print("      + Update ARP table: MAC={} <--> IPv4={}".format(in_smac,_sip))
                #Create ARP reply packet and send it to the request Host
                    for dp in self.datapaths.values():
                        if dp.id in list(self.ARP_table.keys()):
                            ofp = dp.ofproto
                            ofp_parser = dp.ofproto_parser
                        ################# This only success if you send to the host has the different IP network address################### 
                            if _dip in list(self.ARP_table[dp.id].values()):
                                print("   - Creates and return the ARP reply packet2: IPv4={} <--> MAC={}".format(_dip,in_dmac))
                            #if int(_dip.split('.')[2]) == int(_sip.split('.')[2]):
                            
                                e   =   ethernet.ethernet(dst=in_dmac,src=in_smac,ethertype=ether.ETH_TYPE_ARP)
                                a   =   arp.arp ( hwtype=1,proto=0x0800,hlen=6,plen=4,opcode=2,
                                                                                    
                                                                                src_mac=in_smac, src_ip=_sip,
                                                                                dst_mac=in_dmac, dst_ip=_dip)
                                print("-------------------------------------------------------------------")
                                print("     => Sending ARP Reply Packet to Switch {} - port {}".format(dp.id,self.MAC_table[dp.id][in_dmac]))
                                print("-------------------------------------------------------------------")
                                p=packet.Packet()
                                p.add_protocol(e)
                                p.add_protocol(a)
                                p.serialize()
                                ############################################################################################################
                                # Send ARP reply packet to inform the Request Host about the destination MAC address of the destination host
                                #
                                actions = [ofp_parser.OFPActionOutput(self.MAC_table[dp.id][in_dmac])]
                                self.send_packet(dp,buffer,ofp.OFPP_CONTROLLER,actions,p.data)
                                print("Successfully sending Packet out")
                                print("")
                                ################################################################################################################################################################################################
                                # Insert Route if the destination Host and Source Host lie in different subnet.
                                # 
                                dpid_dest = self.Get_dst_dpid(in_smac)
                                first_port = self.MAC_table[dp.id][in_dmac]
                                last_port = self.MAC_table[dpid_dest][in_smac]
                                path_route=[]
                                path_route = self.FindRoute(dp.id,dpid_dest, first_port, last_port, in_smac, in_dmac)
                                print("\n------------------------------------- Route -------------------------------------")
                                print(path_route)
                                print("   - Add flow entries to all OFS on the path route") 

                                for i in range(len(path_route)):
                                    _dp         = self.datapaths[list(path_route.keys())[i]]
                                    _ofp        = _dp.ofproto
                                    _ofp_parser = _dp.ofproto_parser

                                    _pin = path_route[_dp.id][0]
                                    _pout = path_route[_dp.id][1]
                                    # Prepare and send Flow Mod ( add new entry to the OFS)
                                    #Forward
                                    _actions = [_ofp_parser.OFPActionOutput(_pin)]
                                    _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
                                    _match   = _ofp_parser.OFPMatch(eth_dst=in_smac, in_port=_pout)
                                    self.flow_add(_dp, flow_idle_timeout, 2, _match, _inst,in_smac,0,_pout,_dp.id)
                                    
                                    # Backward
                                    _actions = [_ofp_parser.OFPActionOutput(_pout)]
                                    _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
                                    _match   = _ofp_parser.OFPMatch(eth_dst=in_dmac, in_port=_pin)
                                    self.flow_add(_dp,flow_idle_timeout, 2, _match, _inst,in_dmac,0,_pin,_dp.id)
    
            
    ##############################################################################################################################################################################################################################################################
    # Handle ARP if the destination MAC address doesn't learn yet
    #
    def ARP_MAC_not_in_table(self,dpid,smac,sip,dip,ipin,buffer_id):
        p=packet.Packet()
        e=ethernet.ethernet(ethertype=ether.ETH_TYPE_ARP,src=smac,dst='FF:FF:FF:FF:FF:FF') # source MAC address cua h1, broadcast MAC address 
        a=arp.arp(hwtype=1,proto=0x0800,hlen=6,plen=4,opcode=1,
                                        src_mac=smac,src_ip=sip,
                                        dst_mac='FF:FF:FF:FF:FF:FF',dst_ip=dip)
        p.add_protocol(e)
        p.add_protocol(a)
        p.serialize()
        count=0
        count_len=0
        for dp in list(self.datapaths.values()):
            if dp.id in list(self.port_host.keys()) and dp.id ==  int(dip.split('.')[2]):
                ofp = dp.ofproto
                ofp_parser = dp.ofproto_parser
                for port in list(self.port_host[dp.id]):
                    port_out = port
                    print("-------------------------------------------------------------------")
                    print("     => Sending ARP Request Packet to Switch {} - port {}".format(dp.id,port_out))
                    print("-------------------------------------------------------------------")
                                                    
                    actions=[ofp_parser.OFPActionOutput(port_out)]
                    self.send_packet(dp,0,ofp.OFPP_CONTROLLER,actions,p.data)
                                            
               
    
    ################################################################################################################################################################################################
    # Apply rules for UDP to flood to all interfaces except the receive interface
    #
    def UDP_handling(self,in_dpid,in_pin,in_smac,in_dmac,in_ofp_parser,in_dp,in_ofp,in_etherh,in_pkt,datapaths,out_port,buffer,data):
        udp_packet = in_pkt.get_protocol(udp.udp)
        #check IP Protocol and create a match for IP
        if in_etherh.ethertype == ether_types.ETH_TYPE_IP:
            if udp:
                print("Nhan duoc UDP packet")
                udp_src_port = udp_packet.src_port
                udp_dst_port = udp_packet.dst_port
                
                if udp_dst_port == 60:
                    print("\n Success fully received UDP packet from {} to {}".format(in_dpid,udp_dst_port))
                if udp_dst_port == 65534:
                    print("Start")
                    match_udp       =   in_ofp_parser.OFPMatch(eth_type=0x0800,ip_proto = in_proto.IPPROTO_UDP)
                    actions_udp      = [in_ofp_parser.OFPActionOutput(in_ofp.OFPP_FLOOD)] 
                    instructions_udp    = [in_ofp_parser.OFPInstructionActions(in_ofp.OFPIT_APPLY_ACTIONS, actions_udp)]
                    mod = in_ofp_parser.OFPFlowMod(datapath=in_dp, priority=2,
                                            match=match_udp, instructions=instructions_udp)
                    in_dp.send_msg(mod)
                    out = in_ofp_parser.OFPPacketOut(datapath=in_dp,
                                        buffer_id=in_ofp.OFP_NO_BUFFER,
                                        in_port=in_pin, actions=actions_udp,
                                        data=data)
                    in_dp.send_msg(out)
                if udp_dst_port == 65535:
                    print("Stop")

    
    ############################################################################################
    # Port Desc Status Reply
    #
    @set_ev_cls(ofp_event.EventOFPPortDescStatsReply, MAIN_DISPATCHER)
    def port_desc_stats_reply_handler(self, ev):
        switch = ev.msg.datapath
        self.link_capacity.setdefault(switch.id,{})
        #self.logger.info('datapath         '
         #                ' port-in   bytes')
        #self.logger.info('---------------- '
                #        
               #          '-------- --------')
        for p in ev.msg.body:
            #self.logger.info('%016x  %8x %8d ',switch.id,
                    #               p.port_no,p.curr_speed)
            if p.curr_speed !=0:
                self.link_capacity[switch.id][p.port_no] =    p.curr_speed
        self.count_link_capacity += 1
        if self.count_link_capacity == 8:
            print("Link Capacity: {}".format(self.link_capacity))
            self.count_link_capacity = 0
    ###############################################################################################################
    # Sending Port Desc Stats Request
    #
    def sending_port_desc_stats_request(self,dp):
        ofp = dp.ofproto
        ofp_parser = dp.ofproto_parser
        req = ofp_parser.OFPPortDescStatsRequest(dp)
        dp.send_msg(req)
    ############################################################################################
    # Flow Status Reply
    #
    @set_ev_cls(ofp_event.EventOFPFlowStatsReply,MAIN_DISPATCHER)
    def flow_stats_reply(self,ev):
        body = ev.msg.body
        dpid = ev.msg.datapath.id
        times = ev.timestamp
        ####################################################################################################################################################################    
        if len(self.flow_recent_exist_compare) == 0 or self.ready == False:
            if self.the_first_flow_stat_request:
                self.count_flow += 1
                for stat in sorted([flow for flow in body if flow.priority == 2],
                        key=lambda flow: (flow.match['in_port'],
                                            flow.match['eth_dst'])):
                    
                    for each_path in self.flow_recent_exist:
                        if dpid in list(each_path.keys()) and each_path[dpid][0] == stat.match['in_port'] and each_path[dpid][4] == stat.match['eth_dst']:
                            each_path[dpid][2] = stat.byte_count
                            each_path[dpid][3] = times
                       
                if self.count_flow == self.count_switch_in_path:
                    self.the_first_flow_stat_request =  False
                    self.the_second_flow_stat_request = True
                    # print("\nBefore 1: {}".format(self.flow_recent_exist))
                    self.count_flow = 0
                    self.flow_recent_exist_2 = copy.deepcopy(self.flow_recent_exist)
                    self.flow_recent_exist_compare = copy.deepcopy(self.flow_recent_exist)
                    hub.sleep(1)
                    self.send_the_second_flow_stat_request()       

            elif self.the_second_flow_stat_request:
                self.count_flow += 1
                for stat in sorted([flow for flow in body if flow.priority == 2],
                        key=lambda flow: (flow.match['in_port'],
                                            flow.match['eth_dst'])):
                    
                    for each_path in self.flow_recent_exist:
                        if dpid in list(each_path.keys()) and each_path[dpid][0] == stat.match['in_port'] and each_path[dpid][4] == stat.match['eth_dst']:
                            each_path[dpid][2] = stat.byte_count
                            each_path[dpid][3] = times
                            
                if self.count_flow == self.count_switch_in_path:
                    self.the_first_flow_stat_request =  False
                    self.the_second_flow_stat_request = False
                    # print("\nAfter 1: {}".format(self.flow_recent_exist_2))
                    self.count_flow = 0
                    self.ready = True
                    self.estimate_data_rate()

        ##################################################################################################################################################################            
        if len(self.flow_recent_exist_compare) !=0 and self.ready:
            if self.the_first_flow_stat_request:
                position = []
                save = 0
                self.count_flow += 1
                for stat in sorted([flow for flow in body if flow.priority == 2],
                        key=lambda flow: (flow.match['in_port'],
                                            flow.match['eth_dst'])):
                    
                    for each_path in self.flow_recent_exist:
                        if dpid in list(each_path.keys()) and each_path[dpid][0] == stat.match['in_port']  and each_path[dpid][4] == stat.match['eth_dst']:
                            each_path[dpid][2] = stat.byte_count
                            each_path[dpid][3] = times
                                 
                if self.count_flow == self.count_switch_in_path:
                    self.the_first_flow_stat_request =  False
                    self.the_second_flow_stat_request = True
                    for each_path in self.flow_recent_exist_compare:
                        count = 0
                        for paths in self.flow_recent_exist:
                            if each_path.keys() == paths.keys():
                                for sw,ports in list(each_path.items()):
                                    if ports[2] == paths[sw][2] and ports[1] == paths[sw][1]:
                                        count +=1
                                    if count == len(paths):
                                        position.append(save)
                                        save +=1
                                        break
                    
                    if len(position) != 0:
                        for n in range(len(position)):
                            del self.flow_recent_exist[position[n]]
                    self.count_flow = 0
                    self.flow_recent_exist_compare = copy.deepcopy(self.flow_recent_exist)
                    self.flow_recent_exist_2 = copy.deepcopy(self.flow_recent_exist)
                    # print("\nBefore 2: {}".format(self.flow_recent_exist))
                    hub.sleep(1)
                    self.send_the_second_flow_stat_request()
                    
            elif self.the_second_flow_stat_request:
                self.count_flow += 1
                for stat in sorted([flow for flow in body if flow.priority == 2],
                        key=lambda flow: (flow.match['in_port'],
                                            flow.match['eth_dst'])):
                    
                    for each_path in self.flow_recent_exist:
                        if dpid in list(each_path.keys()) and each_path[dpid][0] == stat.match['in_port']  and each_path[dpid][4] == stat.match['eth_dst']:
                            each_path[dpid][2] = stat.byte_count
                            each_path[dpid][3] = times
                            
                if len(self.flow_recent_exist) == 0:
                    self.ready = False            
                if self.count_flow == self.count_switch_in_path:
                    self.the_first_flow_stat_request =  False
                    self.the_second_flow_stat_request = False
                    # print("\nAfter 2: {}".format(self.flow_recent_exist_2))
                    self.count_flow = 0
                    self.estimate_data_rate()
                
            
    """
    Network Topology
    """
    
    ##############################################################
    # Network Changed:
    #   1. Switch is added or removed/unavailable
    #   2. Port status is changed (UP/DOWN)
    #

    #######################################
    # 1a. Switch is added
    @set_ev_cls(event.EventSwitchEnter)
    def handler_switch_enter(self, ev):

        print("\nSwitch entering (Datapath ID = {}) --------------- Log at: {}".format(ev.switch.dp.id, datetime.datetime.now()))
        if(self.network_changed_thread != None):
          hub.kill(self.network_changed_thread)
        self.sending_port_desc_stats_request(ev.switch.dp)
        self.network_changed_thread = hub.spawn_after(1,self.network_changed)

    ###############################################################################################################
    # 1b. Switch is removed/unavailable
    @set_ev_cls(event.EventSwitchLeave)
    def handler_switch_leave(self, ev):

        print("\nSwitch leaving (Datapath ID = {}) --------------- Log at: {}".format(ev.switch.dp.id, datetime.datetime.now()))
        if(self.network_changed_thread != None):
          hub.kill(self.network_changed_thread)
        req = ev.switch.dp.ofproto_parser.OFPPortDescStatsRequest(ev.switch.dp)
        ev.switch.dp.send_msg(req)
        self.network_changed_thread = hub.spawn_after(1,self.network_changed)

    ###############################################################################################################
    # Update the topology
    #   * No care end hosts
    # 
    def network_changed(self):
        print("\nNetwork is changed------------------------------- Log at: {}".format(datetime.datetime.now()))
        self.topo_raw_switches = get_switch(self, None)
        self.topo_raw_links = get_link(self, None)
        
        print("\nCurrent Switches:")
        for s in self.topo_raw_switches:
            print (str(s))
        print("\nCurrent Links:")
        for l in self.topo_raw_links:
            print (str(l))
        self.BuildTopology()


    """
    
    
    Topology Building



    """
    ###############################################################################################################
    # Build topology
    # 
    def BuildTopology(self):
        self.Topology_db.clear()

        for l in self.topo_raw_links:
            _dpid_src = l.src.dpid
            _dpid_dst = l.dst.dpid
            _port_src = l.src.port_no
            _port_dst = l.dst.port_no
            
            self.Topology_db.setdefault(_dpid_src,{})
            self.Switch_switch_db.setdefault(_dpid_src,{})
            self.Topology_db[_dpid_src][_dpid_dst] = _port_src
            self.Switch_switch_db[_dpid_src][_dpid_dst]=[_port_src,_port_dst]
        print("")
        print("   - Topology Database: {}".format(self.Topology_db))
        print("")
        print("   - Switch-Switch Link Database: {}".format(self.Switch_switch_db))

        for l in self.topo_raw_switches:
            dpid_src=l.dp.id
            self.switch_port_connect=[]
            for m in range(len(l.ports)):
                
                self.port_connect = l.ports[m].port_no
                m=m+1
                self.switch_port_connect.append(self.port_connect)
                
            self.port_switch[dpid_src]=self.switch_port_connect   
        print("")
        print("   - All switch-port Database: {}".format(self.port_switch))
        print("")

        for switch in list(self.port_switch.keys()):
            count = 0
            self.port_host_connect = []
            for each_port in list(self.port_switch[switch]):
                count += 1
                if each_port not in list(self.Topology_db[switch].values()):
                    self.port_host_connect.append(each_port)  
                if count == len(self.port_switch[switch]):# and len(self.port_host_connect) != 0:

                    self.port_host[switch]= self.port_host_connect
                    break
        print(self.port_host)

        """
        self.filter_link_connection_between_switch()
        """
        self.data_rate_2 = copy.deepcopy(self.Switch_switch_db)
        self.data_rate_3 = copy.deepcopy(self.Switch_switch_db)
        self.data_rate_estimate = copy.deepcopy(self.Switch_switch_db)
        for switch_port in list(self.data_rate_2.values()):
            for port in list(switch_port.values()):
                port.append(0)
                port.append(0)
        for switch_port in list(self.data_rate_3.values()):
            for port in list(switch_port.values()):
                port.append(0)
                port.append(0)
        for switch_port in list(self.data_rate_estimate.values()):
            for port in list(switch_port.values()):
                port.append(0)
        #self.filter_link_connection_between_switch_for_drop()
        #self.install_drop_rule(30)
        #self.install_forward_controller_rule(60)
        #self.send_udp_train_packet()

    #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#    
    def send_udp_train_packet(self):
        count = 0
        while 1:
            if count == 0:
                
                print(" Jump into the UDP destination port {}".format(45))
                
                count += 1
                for dp in self.datapaths.values():
                    pkt = self.create_udp_packet_control_to_switch(60)
                    pkt.serialize()
                    for key, sw_port in self.Switch_switch_db.items():
                        if key ==  dp.id:
                            for port in sw_port.values():
                                ofp = dp.ofproto
                                ofp_parser = dp.ofproto_parser
                                action = [ofp_parser.OFPActionOutput(ofp.OFPP_CONTROLLER)]
                                self.send_packet(dp,0,ofp.OFPP_CONTROLLER,action,pkt.data)
            elif count == 9:
                
                print(" Jump into the UDP destination port {}".format(60))
                
                for dp in self.datapaths.values():
                    pkt = self.create_udp_packet_control_to_switch(60)
                    pkt.serialize()
                    for key, sw_port in self.Switch_switch_db.items():
                        if key ==  dp.id:    
                            for port in sw_port.values():
                                ofp = dp.ofproto
                                ofp_parser = dp.ofproto_parser
                                action = [ofp_parser.OFPActionOutput(ofp.OFPP_CONTROLLER)]              
                                self.send_packet(dp,0,ofp.OFPP_CONTROLLER,action ,pkt.data)
                count = 0
                break
            else:
                
                print(" Jump into the UDP destination port {}".format(30))
                
                count += 1
                for dp in self.datapaths.values():
                    pkt = self.create_udp_packet_control_to_switch(30)
                    pkt.serialize()
                    for key, sw_port in self.Switch_switch_db.items():
                        if key ==  dp.id:
                            for port in sw_port.values():
                                ofp = dp.ofproto
                                ofp_parser = dp.ofproto_parser
                                action = [ofp_parser.OFPActionOutput(ofp.OFPP_CONTROLLER)]               
                                self.send_packet(dp,0,ofp.OFPP_CONTROLLER,action,pkt.data)
    """
    ###############################################################################################################
    # Filter link connection between switch
    #
    def send_udp_train_packet(self):
        count = 0
        while 1:
            if count == 0:
                pkt = self.create_udp_packet_control_to_switch(60)
                print(" Trump into the UDP destination port {}".format(45))
                pkt.serialize()
                count += 1
                for dp in self.datapaths.values():
                    if dp.id in self.port_host.keys():
                        ofp = dp.ofproto
                        ofp_parser = dp.ofproto_parser
                        action = [ofp_parser.OFPActionOutput(port=self.port_host[dp.id][0])]                
                        self.send_packet(dp,0,ofp.OFPP_CONTROLLER,action,pkt.data)
            elif count == 39:
                pkt = self.create_udp_packet_control_to_switch(60)
                print(" Trump into the UDP destination port {}".format(60))
                pkt.serialize()
                for dp in self.datapaths.values():
                    if dp.id in self.port_host.keys():
                        ofp = dp.ofproto
                        ofp_parser = dp.ofproto_parser
                        action = [ofp_parser.OFPActionOutput(port=self.port_host[dp.id][0])]                
                        self.send_packet(dp,0,ofp.OFPP_CONTROLLER,action,pkt.data)
                count = 0
                break
            else:
                pkt = self.create_udp_packet_control_to_switch(30)
                print(" Trump into the UDP destination port {}".format(30))
                pkt.serialize()
                count += 1
                for dp in self.datapaths.values():
                    if dp.id in self.port_host.keys():
                        ofp = dp.ofproto
                        ofp_parser = dp.ofproto_parser
                        action = [ofp_parser.OFPActionOutput(port=self.port_host[dp.id][0])]                
                        self.send_packet(dp,0,ofp.OFPP_CONTROLLER,action,pkt.data)
            
    """

    ##################################################################################################################
    # Filter the connection between switch to find the capacity of each link
    # 

    def filter_link_connection_between_switch(self):
        for l in range(len(self.Switch_switch_db.keys())):
            self.link_connection_switch.setdefault(self.Switch_switch_db.keys()[l],{})
            for i in range(l+1,len(self.Switch_switch_db.keys())):
                for dp_id in self.Switch_switch_db.values()[i].keys():
                    for dpid in self.Switch_switch_db.values()[l].keys():
                        if dp_id ==  self.Switch_switch_db.keys()[l]:
                            if dpid == self.Switch_switch_db.keys()[i]:
                                self.link_connection_switch[dp_id][dpid]=0
        ############################################################################################################
        for key,values in list(self.link_connection_switch.items()):
            if len(values) == 0:
                del self.link_connection_switch[key]
        #############################################################################################################
        for dp in self.Switch_switch_db.keys():
            if dp in self.link_connection_switch.keys():
                for key in self.link_connection_switch[dp].keys():
                    if key in self.Switch_switch_db.keys():
                            self.link_connection_switch[dp][key] = self.Switch_switch_db[dp][key]  
        print("\n   - All switch-switch link filter: {}".format(self.link_connection_switch))               
    ##################################################################################################################
    # Filter the connection between switch to apply the drop rule
    # 
    def filter_link_connection_between_switch_for_drop(self):
        for dpid in self.Switch_switch_db.keys():
            if dpid not in self.link_connection_switch.keys():
                self.switch_drop.setdefault(dpid,{})
                self.switch_drop[dpid]=self.Switch_switch_db[dpid]
        print("\n   - All destination switch: {}".format(self.switch_drop))

    ###########################################################################################
    # Install the flow rule to drop the UDP packet with dst_port 30
    #
    def install_drop_rule(self,udp_dst):
        for dpid,next_sw_and_port in self.switch_drop.items():
            if dpid in self.datapaths.keys():
                for port in next_sw_and_port.values():
                    dp =  self.datapaths[dpid]
                    ofp = dp.ofproto
                    ofp_parser = dp.ofproto_parser
                    match_udp_drop_i =  ofp_parser.OFPMatch(eth_type=0x0800,ip_proto = in_proto.IPPROTO_UDP,
                                                                        udp_dst=udp_dst, in_port=port[0])
                    self.flow_add(dp,60,1,match_udp_drop_i,None,0,0,0,dp.id)
    #########################################################################################
    # Install the flow rule to forward the UDP packet with dst_port 60 to next_switch
    #
    def install_forward_controller_rule(self,udp_dst):
        for dpid, next_sw_and_port in self.link_connection_switch.items():
            if dpid in self.datapaths.keys():
                
                dp = self.datapaths[dpid]
                ofp = dp.ofproto
                ofp_parser = dp.ofproto_parser
                ####################################################################################
                # Install single flow rule to forward the UDP packet with dst_port 60 to next switch\
                for port in next_sw_and_port.values():
                    match_udp = ofp_parser.OFPMatch(eth_type=0x0800,ip_proto = in_proto.IPPROTO_UDP,udp_dst=udp_dst, in_port=ofp.OFPP_CONTROLLER)
                    actions = [ofp_parser.OFPActionOutput(port[0])]
                    instruction_1 = [ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS,actions)]
                    self.flow_add(dp,60,0,match_udp,instruction_1,0,0,0,dp.id)
                """
                actions=[]
                buckets = []
                if dpid in self.port_host.keys():
                    for port in next_sw_and_port.values():
                        match_udp       =   ofp_parser.OFPMatch(eth_type=0x0800,ip_proto = in_proto.IPPROTO_UDP,udp_dst=udp_dst,in_port=self.port_host[dpid][0])
                        if len(next_sw_and_port) < 2:
                            actions = [ofp_parser.OFPActionOutput(port[0])]
                            instruction = [ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS,actions)]
                            self.flow_add(dp,60,1,match_udp,instruction,0,0,0,dp.id)
                            #print("\n   - Install flow rule to forward the UDP packet with dst_port 60 in switch {}".format(dpid))
                        else:
                            actions.append([ofp_parser.OFPActionOutput(port[0])])

                            if len(actions) == len(next_sw_and_port):
                                for action in actions:
                                    buckets.append(ofp_parser.OFPBucket(actions=action))
                                req = ofp_parser.OFPGroupMod(dp, ofp.OFPGC_ADD,
                                                                    ofp.OFPGT_ALL, 50, buckets)
                                dp.send_msg(req)

                                actions_new = [ofp_parser.OFPActionGroup(group_id=50)]
                                instructions_udp =[ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions_new)]
                                            
                                self.flow_add(dp,60,1,match_udp,instructions_udp,0,0,0,dp.id)
                                #print("\n   - Install Group rule to forward the UDP packet with dst_port 60 in switch {}".format(dpid))
                """
                #####################################################################################################
                # Install the flow rule to forward the UDP packet with dst_port 60 to the controller
                for sw, port in next_sw_and_port.items():
                    if sw in self.datapaths.keys():
                        dp = self.datapaths[sw]
                        ofp = dp.ofproto
                        ofp_parser = dp.ofproto_parser
                        match_udp_controller = ofp_parser.OFPMatch(eth_type=0x0800,ip_proto = in_proto.IPPROTO_UDP,udp_dst=udp_dst, in_port=port[1])
                        actions_controller = [ofp_parser.OFPActionOutput(ofp.OFPP_CONTROLLER, ofp.OFPCML_NO_BUFFER)]
                        instruction = [ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS,actions_controller)]
                        self.flow_add(dp,60,1,match_udp_controller,instruction,0,0,0,dp.id)

                
                


    """

    Function 

    """
    ###############################################################################################################
    # Add Flow
    # 
    def flow_add(self, dp ,idle_timeout, priority, match, instructions,mac,ipv4,port_out,datapath_id):
        ofp = dp.ofproto
        ofp_parser=dp.ofproto_parser
        if instructions == None:
            mod = ofp_parser.OFPFlowMod(datapath=dp, command=ofp.OFPFC_ADD  
                                            , idle_timeout=idle_timeout, priority=priority, match=match)
        else:                                    
            mod        = ofp_parser.OFPFlowMod(datapath=dp, command=ofp.OFPFC_ADD, 
                                            idle_timeout=idle_timeout, priority=priority, 
                                            
                                            match=match, instructions=instructions)
        if priority == 0:
            in_port = "Any"
            eth_dst = "Any"
            print("\n      + FlowMod (ADD) of Datapath ID={}, Match: (Dst. MAC={}, PortIn={}), Action: (PortOut={})".format(
            dp.id, eth_dst, in_port, instructions[0].actions[0].port))
        else:
            if ipv4 != 0 :
                print("\n      + FlowMod (ADD) of Datapath ID={}, Match: (Dst. MAC={}, IPv4={}), Action: (PortOut={})".format(
                                                        datapath_id, mac,ipv4 , port_out ))
            else:
                print("\n      + FlowMod (ADD) of Datapath ID={}, Match: (Dst. MAC={}, In-port={}), Action: (PortOut={})".format(
                                                        datapath_id, mac,match['in_port'] , port_out ))    
            
        dp.send_msg(mod)
    
    ###############################################################################################################
    #  Flow Remove
    # 
    def flow_remove(self,dp,match):
        ofp         = dp.ofproto
        ofp_parser  = dp.ofproto_parser
        mod         = ofp_parser.OFPFlowMod(datapath=dp,command = ofp.OFPFC_DELETE, out_port = ofp.OFPP_ANY,out_group=ofp.OFPP_ANY,match=match)
        print ("        + Flow (REMOVE) of Datapath ID = {}, Match: (Destination MAC = {})".format(dp.id,match["eth_dst"]))
        dp.send_msg(mod)

    ###############################################################################################################

    ###############################################################################################################
    # Send Packet
    # 
    def send_packet(self, datapaths,buffer_id, in_port,actions, data):
        ofproto=datapaths.ofproto
        ofp_parser=datapaths.ofproto_parser

        if buffer_id != 0 : 
            out = ofp_parser.OFPPacketOut(datapath = datapaths, buffer_id = buffer_id,
                                                            in_port=in_port, actions = actions, data = data)
        else:
            out = ofp_parser.OFPPacketOut(datapath = datapaths, buffer_id = ofproto.OFP_NO_BUFFER,
                                                                in_port = in_port, actions = actions, data = data)
        datapaths.send_msg(out)
   
    ##########################################
    # Count the number of switches
    # 
    def switches_count(self):
        return len(self.topo_raw_switches)

    ######################################################################################################################
    # Create random ASCII string data for measure the link capacity from switch to controller and from switch to switch
    #
    def get_random_string_data(self,length):
    # choose from all lowercase letter
        letters = string.ascii_lowercase
        result_str = ''.join(random.choice(letters) for i in range(length))
        #print("Random string of length", length, "is:", result_str)
        return result_str
    ######################################################################################################################
    # Create UDP Packet to measure the RTT between switch and controller   
    def create_udp_packet_control_to_switch(self,port):
        # Create UDP Packet
        e = ethernet.ethernet(ethertype = 0x0800,dst="FF:FF:FF:FF:FF:FF")
        i = ipv4.ipv4(version=4,src="255.255.255.255",proto=17)
        u = udp.udp(dst_port=port)
        data = self.get_random_string_data(982)
        p = packet.Packet()
        p.add_protocol(e)
        p.add_protocol(i)
        p.add_protocol(u)
        p.add_protocol(data)
        return p
    ###############################################################################################################
    # Looking for the Switch IP based on destination MAC address Host and ARP_table
    #
    def Get_dst_dpid(self,mac):
        for dpid in self.ARP_table.keys():
            if mac in self.ARP_table[dpid].keys():
                return dpid
    ################################################################################################################
    # Find the exit interface of a switch
    #
    def Get_port_out (self,dpid_src,dpid_dst,mac):
        # Destination is on the same Switch:
        if dpid_src == dpid_dst:
            return self.MAC_table[dpid_src][mac]

        return self.Topology_db[dpid_src][dpid_dst][0]
    ################################################################################################################
    # Send Flow Stats Request Packet
    def send_flow_stat_request(self,dp,port_in,port_out,mac):
        ofp = dp.ofproto
        ofp_parser = dp.ofproto_parser
        
        match = ofp_parser.OFPMatch(eth_dst=mac, in_port= port_in)
        flow_request = ofp_parser.OFPFlowStatsRequest(datapath = dp, match=match)
        dp.send_msg(flow_request)
    """
    
    
    Load balancing function

    
    """


    ################################################################################################################
    # Find route
    #
    def FindRoute(self,dpid_src,dpid_dst,first_port,last_port,dmac,smac):
        first_port = first_port
        last_port = last_port
        dmac = dmac
        smac = smac
        # Case 1: Destination is on the same Switch:
        if dpid_src == dpid_dst:
            return [dpid_src]
        else:
        # Case 2: Destination is on another Switch:
            paths = []
            stack = [(dpid_src, [dpid_src])]
            while stack:
                (node, path) = stack.pop()
                for next_node in set(list(self.Topology_db[node].keys())) - set(path):
                    if next_node == dpid_dst:
                        paths.append(path + [next_node])
                    else:
                        stack.append((next_node, path + [next_node]))
            # print (" Available paths from {}  to  {}: {}".format(dpid_src, dpid_dst,paths))
            reserve_paths=self.paths_reserve(paths)
            # print (" Available reserved paths from {}  to  {}: {}".format(dpid_src, dpid_dst,reserve_paths))
            self.filter_switch_to_switch_connection(paths,reserve_paths)
            self.save_path_with_port = self.add_port_to_path(paths,reserve_paths,first_port , last_port)[1]
            ############################################### Print for the test #################################
            print("")
            print(" Print for the path with port : {}".format(self.save_path_with_port))
             
            self.path_and_cost = copy.deepcopy(self.save_path_with_port)
      
            #self.estimate_cost_path(reserve_paths,paths,first_port,last_port,dmac,smac)
            # The best route is the route having the 'minimum cost path'
            
            if len(self.flow_recent_exist) == 0:
                sum_of_cost = []
                for path in self.path_and_cost:
                    save = 0
                    for swid,port in path.items():
                        save += port[2]
                    sum_of_cost.append(save)
                minpos = sum_of_cost.index(min(sum_of_cost))
                self.flow_recent_exist.append(self.path_and_cost[minpos])
                # print("\n Flow_recent_exist 1: {}".format(self.flow_recent_exist))            
                return self.path_and_cost[minpos]
            else:
                if self.have_replica_flow:
                    self.data_rate_estimate_copy = copy.deepcopy(self.data_rate_estimate)
                    sum_of_cost = []
                    for each_path in self.data_rate_estimate:
                        save = 0
                        for sw, ports in list(each_path.items()):
                            save += ports[2]
                        sum_of_cost.append(save)

                    for each_path in self.path_and_cost:
                        for path in self.data_rate_estimate:
                            if each_path.keys() == path.keys():
                                for sw, ports in list(path.items()):
                                    self.path_and_cost[sw][2] += ports[2]
                    self.estimate_link_cost_dict()

                    ################################## Sorted self.data_rate_estimate ###############################################
                    self.data_rate_estimate = []
                    self.data_rate_estimate =  [x for self.data_rate_estimate_copy, x in sorted(zip(sum_of_cost,self.data_rate_estimate_copy))]
                    # print(self.data_rate_estimate)
                else:
                    sum_of_cost = []
                    for each_path in self.path_and_cost:
                        for path in self.data_rate_estimate:
                            if each_path.keys() == path.keys():
                                for sw,ports in list(path.items()):
                                    each_path[sw][2] = each_path[sw][2] + ports[2]

                    self.estimate_link_cost_dict()
                    # print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
                    # print(self.path_and_cost)
                    count = 0
                    for each_path in self.path_and_cost:
                        for path in self.data_rate_estimate:
                            if each_path.keys() == path.keys():
                                count += 1 
                                break
                    if count != len(self.path_and_cost):
                        for path in self.path_and_cost:
                            save = 0
                            for swid,port in path.items():
                                save += port[2]
                            sum_of_cost.append(save)
                        minpos = sum_of_cost.index(min(sum_of_cost))
                        self.flow_recent_exist.append(self.path_and_cost[minpos])
                        # print("\n Flow_recent_exist 2: {}".format(self.flow_recent_exist))            
                        return self.path_and_cost[minpos]
                    else:
                        self.relocate_the_flow()
                        
                        for path in self.path_and_cost:
                            save = 0
                            count = 0
                            for each_path in self.data_rate_estimate:
                                count +=1
                                if each_path.keys() == path.keys():
                                    for swid,port in each_path.items():
                                        save+= port[2]
                                if count == len(self.data_rate_estimate):
                                    sum_of_cost.append(save)
                        minpos = sum_of_cost.index(min(sum_of_cost))
                        self.flow_recent_exist.append(self.path_and_cost[minpos])
                        #print("\n Flow_recent_exist 3: {}".format(self.flow_recent_exist))
                        self.have_replica_flow = True
                        return self.path_and_cost[minpos]
                        

                        

                
    ###################################################################################################################
    # Reserve the path
    #
    def paths_reserve(self,paths):
        reserve_paths = []
        for array in paths:
            reserve_paths.append(array[::-1])
        #print(reserve_paths)
        return reserve_paths
    
    ###################################################################################################################
    # Filter the switch-to-switch connection
    #
    def filter_switch_to_switch_connection(self,paths,reserve_paths):
        self.paths_dic = {}
        self.paths_reserve_dic = {}
        

        for path in paths:
            for i in range(len(path)-1):
                self.paths_dic.setdefault(path[i],[])
                self.paths_dic[path[i]].append(path[i+1])
        
        for path in reserve_paths:
            for i in range(len(path)-1):
                self.paths_reserve_dic.setdefault(path[i],[])
                self.paths_reserve_dic[path[i]].append(path[i+1])
        
        for keys, values in self.paths_reserve_dic.items():
            if len(values) > 1:
                self.paths_reserve_dic[keys]=list(set(values))
        for keys, values in self.paths_dic.items():
            if len(values) > 1:
                self.paths_dic[keys]=list(set(values))
        
        #print( "\n Path reserve dictionary: {}".format(self.paths_reserve_dic))
        #print("\n Path dictionary: {}".format(self.paths_dic))
    ##########################################################################################################
    # Calculate the weight of bucket for each path and reserve path
    #
    def add_port_to_path(self,paths,reserve_paths,first_port, last_port):
        """
        Add the ports that connects the switches for all paths
        """
        paths_p = []
        paths_p_reserve = []
        for paths in paths:
            p = {}
            in_port = first_port
            for s1, s2 in zip(paths[:-1], paths[1:]):
                out_port = self.Topology_db[s1][s2]
                p[s1] = [in_port, out_port,0,0]
                in_port =  self.Topology_db[s2][s1]
            p[paths[-1]] = [in_port, last_port,0,0]
            paths_p.append(p)
    
        for paths in reserve_paths:
            p_reserve = {}
            in_port = last_port
            for s1, s2 in zip(paths[:-1], paths[1:]):
                out_port = self.Topology_db[s1][s2]
                p_reserve[s1] = [ in_port, out_port,0,0,0]
                in_port =  self.Topology_db[s2][s1]
            p_reserve[paths[-1]] = [ in_port, first_port,0,0,0]
            paths_p_reserve.append(p_reserve)
        #print("\n Paths reserve with port: {}".format(paths_p_reserve))
        for paths in paths_p_reserve:
            mac = self.find_mac_address(list(paths.keys())[-1],paths[list(paths.keys())[-1]][1])
            for sw,ports in list(paths.items()):
                ports[4] = mac

        return [paths_p,paths_p_reserve]
    #############################################################################################################
    # Estimate data rate
    #      
    def estimate_data_rate(self):

        self.data_rate_estimate = copy.deepcopy(self.flow_recent_exist)
        for n in range(len(self.flow_recent_exist)):
            if self.flow_recent_exist[n].keys() == self.flow_recent_exist_2[n].keys():
                for sw,ports in list(self.flow_recent_exist[n].items()):
                    if ports[1] == self.flow_recent_exist_2[n][sw][1]:
                        if ports[3] != self.flow_recent_exist_2[n][sw][3]:
                            bytes_1 = ports[2]
                            bytes_2 = self.flow_recent_exist_2[n][sw][2]
                            times_1 = ports[3]
                            times_2 = self.flow_recent_exist_2[n][sw][3]
                            self.data_rate_estimate[n][sw][2] = round(float((bytes_2 - bytes_1)/( times_2-times_1)),2)
                        else:
                            bytes_1 = 0
                            bytes_2 = 0
                            times_1 = 1
                            times_2 = 2
                            self.data_rate_estimate[n][sw][2] = round(float((bytes_2 - bytes_1)/( times_2-times_1)),2)
        print(" \n Data rate dictionary : ")
        for each_path in self.data_rate_estimate:
            for n in range(len(each_path)):
                if n == len(each_path):
                    sw = list(each_path.keys())[n]
                    if each_path[sw][2] == 0:
                        each_path[sw][2] = each_path[list(each_path.keys())[n-1]][2]
                if n == 0:
                    sw = list(each_path.keys())[n]
                    if each_path[sw][2] == 0:
                        each_path[sw][2] = each_path[list(each_path.keys())[n+1]][2]
            print( " -> {}".format(each_path))
        
    ###################################################################################################################
    # Estimate the cost of each link
    #
    def estimate_link_cost_dict(self):
        for each_path in self.path_and_cost:
            for sw, ports in list(each_path.items()):
                if ports[0] in self.link_capacity[sw].keys():
                    ports[2] = float(ports[2] / self.link_capacity[sw][ports[0]])

        
        print("\n------------------------------ Estimate link ultility ---------------------------------------------")
        print(" \n Estimate link ultility of each link in path:")            
        for each_path in self.path_and_cost:
            print("\n -> {}".format(each_path))
            for sw, ports in list(each_path.items()):
                save = ports[2]

                if 0 < save and save < float(1/3) or math.isclose(save,0):
                    ports[2] = ports[2]

                elif float(1/3) < save and save < float(2/3) or math.isclose(save,1/3):
                    ports[2] = float(3*ports[2]-2/3)

                elif float(2/3) < save and save < float(9/10) or math.isclose(save,2/3):
                    ports[2] = float(10*ports[2]-16/3)

                elif float(9/10) < save and save < 1 or math.isclose(save,9/10):
                    ports[2] = float(70*ports[2]-178/3)

                elif 1 < save and save < float(11/10) or math.isclose(save,1) :
                    ports[2] = float(500*ports[2]-1468/3)

                else:
                    ports[2] = float(5000*ports[2]-16318/3)

        print("\n ------------------------------ Estimate link cost ---------------------------------------------")
        print(" \n Estimate link cost of each link in path:")
        for each_path in self.path_and_cost:
            print("\n -> {}".format(each_path))
        print("\n -----------------------------------------------------------------------------------------------")
        
    #############################################################################################################
    # Group Mod Packet send
    # 
    def group_add(self, dp, bucket_weight, out_port, buckets):   
        
        ofp = dp.ofproto
        ofp_parser = dp.ofproto_parser
        bucket_action = [ofp_parser.OFPActionOutput(out_port)]
        buckets.append( ofp_parser.OFPBucket(
                            weight = bucket_weight,
                            watch_port = out_port,
                            watch_group = ofp.OFPG_ANY,
                            actions = bucket_action
        ))
        return buckets
    ####################################################################################################################
    # Monitor the data_rate
    # 
    def monitor(self):
       while 1:
            hub.sleep(10)
            
            count = 0
            if len(self.flow_recent_exist) != 0:
                self.count_switch_in_path = 0
                
                for each_path in self.flow_recent_exist:
                    count = 0
                    for sw,ports in list(each_path.items()):
                        count += 1
                        self.count_switch_in_path += 1
                        if count != len(each_path):
                            self.the_first_flow_stat_request = True
                            self.the_second_flow_stat_request = False
                            dp = self.datapaths[sw]
                            mac = ports[4]
                            self.send_flow_stat_request(dp,ports[0],0,mac)
                        else:
                            dp = self.datapaths[sw]
                            mac = ports[4]
                            self.send_flow_stat_request(dp,ports[0],0,mac)
                            count = 0
                            break
                
                
    def send_the_second_flow_stat_request(self):
        count = 0
        if len(self.flow_recent_exist) != 0:
            self.count_switch_in_path = 0
            for each_path in self.flow_recent_exist:
                count = 0
                for sw,ports in list(each_path.items()):
                    count += 1
                    self.count_switch_in_path += 1
                    if count != len(each_path):
                        self.the_first_flow_stat_request = False
                        self.the_second_flow_stat_request = True                     
                        dp = self.datapaths[sw]
                        mac = ports[4]
                        self.send_flow_stat_request(dp,ports[0],0,mac)
                    else:
                        dp = self.datapaths[sw]
                        mac = ports[4]
                        self.send_flow_stat_request(dp,ports[0],0,mac)
                        count = 0
                        break            

    ##################################################################################################################################
    # Find MAC address based on port and sw_id
    # 
    def find_mac_address(self,sw_id,port):
        for mac, ports in list(self.MAC_table[sw_id].items()):
            if ports == port: 
                return mac
                break       
    ##################################################################################################################################
    # Relocate the flow 
    #
    def relocate_the_flow(self):
        ################################# Make sure one path is always empty#################################
        sum_of_cost = []
        position_of_change = []
        flow_remove = []
        for path in self.path_and_cost:
            save = 0
            for swid,port in path.items():
                save += port[2]
            sum_of_cost.append(save)
        minpos = sum_of_cost.index(min(sum_of_cost))
        minpos_second = sum_of_cost.index(sorted(sum_of_cost)[1])
        print("\n All the flow in stack:")

        change_path = copy.deepcopy(self.path_and_cost[minpos_second])
        save = 0
        for each_path in self.data_rate_estimate:
            if each_path.keys() == self.path_and_cost[minpos].keys():
                position_of_change.append(save)
                save +=1
            print(" -> {}".format(each_path))

        print("\n Total sum of path:")
        for n in range(len(self.path_and_cost)):
            print("   ","=>".join(map(str,self.path_and_cost[n].keys())),": {}".format(sum_of_cost[n]))
        print("\n The path has the smallest sum: {}".format(list(self.data_rate_estimate[minpos].keys())))

        for sw, ports in list(change_path.items()):
            for element in position_of_change:
                if sw == list(self.path_and_cost[element].keys())[-1]:
                    change_path[sw][1] = self.data_rate_estimate[minpos][sw][1]
                    
                    flow_remove.append(self.data_rate_estimate[minpos])
                    break
        print("\n The flow was chosen to remove: {} ".format(flow_remove))
        print("\n The path where the previous flow will be added to : {}".format(change_path))

        # Add new flow to prepare change the old flow
        print("\n ----------------------------------------------- Add New Flow -------------------------------------------------")
        for sw, ports in list(change_path.items()):
            _dp = self.datapaths[sw]
            _ofp = _dp.ofproto
            _ofp_parser = _dp.ofproto_parser
            _pin = change_path[sw][1]
            _pout = change_path[sw][0]
            in_smac = self.find_mac_address(list(change_path.keys())[-1],change_path[list(change_path.keys())[-1]][1])
            in_dmac = self.find_mac_address(list(change_path.keys())[0],change_path[list(change_path.keys())[0]][0])
            ports[4] = in_smac
            #Forward
            _actions = [_ofp_parser.OFPActionOutput(_pout)]
            _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
            _match   = _ofp_parser.OFPMatch(eth_dst=in_dmac, in_port=_pin)
            self.flow_add(_dp, flow_idle_timeout, 2, _match, _inst,in_dmac,0,_pout,_dp.id)
            
            # Backward
            _actions = [_ofp_parser.OFPActionOutput(_pin)]
            _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
            _match   = _ofp_parser.OFPMatch(eth_dst=in_smac, in_port=_pout)
            self.flow_add(_dp,flow_idle_timeout, 2, _match, _inst,in_smac,0,_pin,_dp.id)
        self.flow_recent_exist.append(change_path)
        self.data_rate_estimate.append(change_path)
        # Remove the previous flow :
        
        print("\n ----------------------------------------------- Remove Flow -------------------------------------------------")
        for sw, ports in list(flow_remove[0].items()):
            _dp = self.datapaths[sw]
            _ofp = _dp.ofproto
            _ofp_parser = _dp.ofproto_parser
            _pin  =  ports[1]
            _pout = ports[0]
            in_smac = self.find_mac_address(list(change_path.keys())[-1],change_path[list(change_path.keys())[-1]][1])
            in_dmac = self.find_mac_address(list(change_path.keys())[0],change_path[list(change_path.keys())[0]][0])
            self.remove_flow(_dp,2,_pout,in_dmac,_pin)
            self.remove_flow(_dp,2,_pin,in_smac,_pout)
        del(self.flow_recent_exist[minpos])
        del(self.data_rate_estimate[minpos])

        for path in self.path_and_cost:
            count = 0
            for each_path in self.data_rate_estimate:
                if each_path.keys() != path.keys():
                    count +=1
                if count == len(self.data_rate_estimate):
                    for sw, ports in list(path.items()):
                        ports[2] = 0

       
    ##################################################################################################################################
    # Remove the flow 
    #        
    def remove_flow(self,dp,priority,out_port,mac,pin):
        
        ofp = dp.ofproto
        ofp_parser = dp.ofproto_parser
        
        match = ofp_parser.OFPMatch(eth_dst = mac,in_port = pin)

        flow_remove = ofp_parser.OFPFlowMod(datapath = dp, priority = priority, out_port = out_port 
                                                        , command = ofp.OFPFC_DELETE_STRICT, match = match )
        print("\n      + FlowMod (Remove) of Datapath ID={}, Match: (Dst. MAC={}, PortIn={}), Action: (PortOut={})".format(
            dp.id, mac, pin, out_port))
        dp.send_msg(flow_remove)

    ############################################################################################################################################
    # Relocate flows periodically
    #
    def relocate_flow_periodically(self):
        while 1:
            hub.sleep(15)
            if self.have_replica_flow:
                print("\n---------------------------------- Period checking ------------------------------------------------")
                print("\n Warning there have been replicated flows existed")
                sum_of_cost = []
                origin_position = []

                count_origin = 0
                for n in range(len(self.data_rate_estimate)):
                    save = []
                    save.append(n)
                    for j in range(n+1,len(self.data_rate_estimate)):
                        if self.data_rate_estimate[n].keys() == self.data_rate_estimate[j].keys():
                            save.append(j)
                    if len(origin_position) != 0:
                        for each_element in origin_position:
                            if isinstance(each_element, list):
                                if len(save) != 1:
                                    for element in save:
                                        if element in each_element:
                                            save = []
                                else:
                                    if save[0] in each_element:
                                        save = []
                        if len(save) !=0:
                            origin_position.append(save)
                    else:
                        if len(save) == 1:
                            origin_position.append(save)
                        else: 
                            origin_position.append(save)
                print("\n My origin position : {}".format(origin_position))

                for each_path in self.data_rate_estimate:
                    save = 0
                    for sw, ports in list(each_path.items()):
                        save += ports[2]
                    sum_of_cost.append(save)

                for i in range(len(sum_of_cost)-1):
                
                    if i == 0 or i == 1:
                        continue
                    else: 
                        b = itertools.combinations(sum_of_cost,i)
                        count = 0
                        path_2 = []
                        path_3 = []
                        path_1 = []
                        path_1_cal = []
                        path_2_cal =  []
                        path_3_cal = []
                        variance = []
                        calculate_variance = []
                        print("\n Sum of cost: {}".format(sum_of_cost))
                        for pair in b:
                            sum_of_cost_compare = copy.deepcopy(sum_of_cost)
                            for element in pair:
                                if element in sum_of_cost_compare:
                                    sum_of_cost_compare.remove(element)
                            if len(sum_of_cost_compare) == MAX_PATH - 1:
                                path_2.append(sum_of_cost_compare[0])
                                path_3.append(sum_of_cost_compare[1])
                                path_1.append(pair)

                        for each_path in path_1:
                            if  isinstance(each_path,tuple):
                                save = sum(list(each_path))
                                path_1_cal.append(save)
                                
                            else:
                                save = each_path
                                path_1_cal.append(save)
                                
                        
                        for each_path in path_2:
                            if  isinstance(each_path,tuple):
                                save = sum(list(each_path))
                                path_2_cal.append(save)
                                
                            else:
                                save = each_path
                                path_2_cal.append(save)
                                

                        for each_path in path_3:
                            if  isinstance(each_path,tuple):
                                save = sum(list(each_path))
                                path_3_cal.append(save)
                                
                            else:
                                save = each_path
                                path_3_cal.append(save)

                        for n in range(len(path_3)):
                            calculate_variance.append([path_1_cal[n],path_2_cal[n],path_3_cal[n]])
                        
                        for each_path in calculate_variance:
                            save = np.var(each_path)
                            variance.append(save)
                        
                        minpos = variance.index(min(variance))
                        print("\n Optimal path : {}".format([path_1[minpos],path_2[minpos],path_3[minpos]]))

                        path_1_change = []
                        path_3_change = []
                        path_2_change = []
                        if isinstance(path_1[minpos],tuple):
                            for each_element in path_1[minpos]:
                                location = sum_of_cost.index(each_element)
                                path_1_change.append(location)
                        else:
                            path_1_change.append(sum_of_cost.index(path_1[minpos]))

                        if isinstance(path_2[minpos],tuple):
                            for each_element in path_2[minpos]:
                                location = sum_of_cost.index(each_element)
                                path_2_change.append(location)
                        else:
                            path_2_change.append(sum_of_cost.index(path_2[minpos]))

                        if isinstance(path_3[minpos],tuple):
                            for each_element in path_3[minpos]:
                                location = sum_of_cost.index(each_element)
                                path_3_change.append(location)
                        else:
                            path_3_change.append(sum_of_cost.index(path_3[minpos]))
                        
                        
                        self.check_and_relocate_flow(path_1_change,path_2_change, path_3_change,origin_position)

    #################################################################################################################################
    # Check and Relocate the flow
    #
    def check_and_relocate_flow(self,path_1,path_2,path_3,origin_position):
        new_position = [path_1,path_2,path_3]
        print(" \n New position: {}".format(new_position))
        for each_element in new_position:
            if each_element in origin_position:
                no_change = True
            else:
                no_change = False
                break
        #print(no_change)

        if no_change == False:
            print("\n The position is ideal ? => {}".format(no_change))
            for each_element in new_position:
                if each_element in origin_position:
                   new_position.remove(each_element)
                   new_position.insert(origin_position.index(each_element),each_element)

            dict_for_change = {}    
            for each_element in new_position:
                if isinstance(each_element,list):
                    for element in each_element:
                        for n in origin_position:
                            if len(n) == 1 and n[0] == element:
                                dict_for_change[element] = [origin_position.index(n)+1,new_position.index(each_element)+1]
                            if len(n) != 1 and element in n:
                                dict_for_change[element] = [origin_position.index(n)+1,new_position.index(each_element)+1]
            
            print(" \n Dictionary for changing: {}".format(dict_for_change))
            
            path_change_save = []
            path_remove_save = []
            self.data_rate_estimate_copy = copy.deepcopy(self.data_rate_estimate)
            for key,values in list(dict_for_change.items()):
                if values[0] == values[1]:
                    continue
                else:
                    
                    path_remove = self.data_rate_estimate_copy[key]
                    for new_key, new_value in list(dict_for_change.items()):
                        if dict_for_change[key][1] == new_value[0] and key != new_key:
                            path_change = self.data_rate_estimate_copy[new_key]
                            break
                    count = 0
                    #print("\n Path Change old: {}".format(path_change))
                    #print("\n Path remove : {}".format(path_remove))
                    for sw,ports in list(path_change.items()):
                        count += 1
                        if count == len(path_change):
                            ports[2] = path_remove[list(path_remove.keys())[count-1]][2]
                            ports[4] = path_remove[list(path_remove.keys())[count-1]][4]
                            ports[1] = path_remove[list(path_remove.keys())[count-1]][1]
                            count = 0
                        else:
                            ports[2] = path_remove[list(path_remove.keys())[count-1]][2]

                            ports[4] = path_remove[list(path_remove.keys())[count-1]][4]
                    
                    #print("\n Path change new: {}".format(path_change))

                    ## Add new Flow
                    print("\n ----------------------------------------------- ADD Flow-------------------------------------------------")
                    for sw, ports in list(path_change.items()):
                        _dp = self.datapaths[sw]
                        _ofp = _dp.ofproto
                        _ofp_parser = _dp.ofproto_parser
                        _pin = path_change[sw][1]
                        _pout = path_change[sw][0]
                        in_smac = self.find_mac_address(list(path_change.keys())[-1],path_change[list(path_change.keys())[-1]][1])
                        in_dmac = self.find_mac_address(list(path_change.keys())[0],path_change[list(path_change.keys())[0]][0])
                        ports[4] = in_smac

                        #Forward
                        _actions = [_ofp_parser.OFPActionOutput(_pout)]
                        _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
                        _match   = _ofp_parser.OFPMatch(eth_dst=in_dmac, in_port=_pin)
                        self.flow_add(_dp, flow_idle_timeout, 2, _match, _inst,in_dmac,0,_pout,_dp.id)
                        
                        # Backward
                        _actions = [_ofp_parser.OFPActionOutput(_pin)]
                        _inst    = [_ofp_parser.OFPInstructionActions(_ofp.OFPIT_APPLY_ACTIONS, _actions)]
                        _match   = _ofp_parser.OFPMatch(eth_dst=in_smac, in_port=_pout)
                        self.flow_add(_dp,flow_idle_timeout, 2, _match, _inst,in_smac,0,_pin,_dp.id)
                    path_change_save.append(path_change)
                    

                    # Remove the previous flow :
        
                    print("\n ----------------------------------------------- Remove Flow-------------------------------------------------")
                    for sw, ports in list(path_remove.items()):
                        _dp = self.datapaths[sw]
                        _ofp = _dp.ofproto
                        _ofp_parser = _dp.ofproto_parser
                        _pin  =  ports[1]
                        _pout = ports[0]
                        in_smac = self.find_mac_address(list(path_change.keys())[-1],path_change[list(path_change.keys())[-1]][1])
                        in_dmac = self.find_mac_address(list(path_change.keys())[0],path_change[list(path_change.keys())[0]][0])
                        self.remove_flow(_dp,2,_pout,in_dmac,_pin)
                        self.remove_flow(_dp,2,_pin,in_smac,_pout)
                    path_remove_save.append(path_remove)

            for path in path_remove_save:
                count = 0
                
                for each_path in self.data_rate_estimate:
                    count += 1 
                    if each_path.keys() == path.keys():
                        for sw, ports in list(path.items()):
                            if ports[3] == each_path[sw][3]:
                                del(self.flow_recent_exist[count-1])
                                del(self.data_rate_estimate[count-1])
                                break

            for path in path_change_save:
                self.flow_recent_exist.append(path)
                self.data_rate_estimate.append(path)
            
        else:
            print("\n The location is ideal ? => {}".format(no_change))
            print ( " \n -> No change requirement")    

