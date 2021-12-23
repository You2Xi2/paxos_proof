include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_agreement_invariants.dfy"

module Proof_Helper {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Agreement_Invs


lemma Lemma_DecidedImpliesQuorumOfAccepts(c:Constants, ds:DistrSys, idx:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx) && LeaderHasDecided(c, ds, idx);
    requires LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
    requires LeaderHasQuorumOfAccepts(c, ds, idx)
    ensures exists qrm :: QuorumOfAcceptMsgs(c, ds, qrm, ds.leaders[idx].ballot)
{
    var l, b := ds.leaders[idx], ds.leaders[idx].ballot;
    var qrm:set<Packet> := {};
    var accepts := l.accepts;
    var sentPackets := ds.network.sentPackets;
    var i := 0;
    while i < c.f + 1 
        decreases c.f+1 - i
        invariant |accepts| == c.f+1 - i
        invariant |qrm| == i
        invariant UniqueSources(qrm)
        invariant forall s | s in accepts :: 
            (forall p | p in qrm :: p.src != s)
        invariant forall s | s in accepts :: s in l.accepts
        invariant forall p | p in qrm :: p.msg.Accept?
        invariant forall p | p in qrm :: p.msg.bal == b
        invariant forall p | p in qrm :: p in sentPackets;
        invariant forall p | p in qrm :: p.dst == Id(Ldr, idx);
    {
        var s :| s in accepts;
        var pkt := Packet(s, Id(Ldr, idx), Accept(b));
        qrm := qrm + {pkt};
        accepts := accepts - {s};
        i := i + 1;
    }
    assert QuorumOfAcceptMsgs(c, ds, qrm, b);
}



lemma lemma_QuorumIntersection(c:Constants, ds:DistrSys, p1_qrm:set<Packet>, p1_bal:Ballot, p2_qrm:set<Packet>, p2_bal:Ballot)
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