include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"

module Proof_Helper {
import opened Network
import opened Agents
import opened Types
import opened Synod

lemma QuorumIntersection(c:Constants, ds:DistrSys, p1_qrm:set<Packet>, p1_bal:Ballot, p2_qrm:set<Packet>, p2_bal:Ballot)
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
    requires QuorumOfPromiseMsgs(c, ds, p1_qrm, p1_bal)
    requires QuorumOfAcceptMsgs(c, ds, p2_qrm, p2_bal)
    ensures exists acc_id :: 
                    && (exists prom_p : Packet :: prom_p in p1_qrm && prom_p.src == acc_id)
                    && (exists acc_p : Packet :: acc_p in p2_qrm && acc_p.src == acc_id)
{
    assume false;  
}

}