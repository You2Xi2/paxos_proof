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


// lemma Lemma_DecidedImpliesQuorumOfAccepts(c:Constants, ds:DistrSys, idx:int) 
//     requires c.WF() && ds.WF(c)
//     requires c.ValidLdrIdx(idx) && LeaderHasDecided(c, ds, idx);
//     requires LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
//     requires LeaderHasQuorumOfAccepts(c, ds, idx)
//     ensures exists qrm :: QuorumOfAcceptMsgs(c, ds, qrm, ds.leaders[idx].ballot)
// {
//     var l, b, v := ds.leaders[idx], ds.leaders[idx].ballot, ds.leaders[idx].val;
//     var qrm:set<Packet> := {};
//     var accepts := l.accepts;
//     var sentPackets := ds.network.sentPackets;
//     var i := 0;
//     while i < c.f + 1 
//         decreases c.f+1 - i
//         invariant |accepts| == c.f+1 - i
//         invariant |qrm| == i
//         invariant UniqueSources(qrm)
//         invariant forall s | s in accepts :: 
//             (forall p | p in qrm :: p.src != s)
//         invariant forall s | s in accepts :: s in l.accepts
//         invariant forall p | p in qrm :: p.msg.Accept?
//         invariant forall p | p in qrm :: p.msg.bal == b
//         invariant forall p | p in qrm :: p in sentPackets;
//         invariant forall p | p in qrm :: p.dst == Id(Ldr, idx);
//     {
//         var s :| s in accepts;
//         var pkt := Packet(s, Id(Ldr, idx), Accept(b, v));
//         qrm := qrm + {pkt};
//         accepts := accepts - {s};
//         i := i + 1;
//     }
//     assert QuorumOfAcceptMsgs(c, ds, qrm, b);
// }



lemma {:timeLimitMultiplier 2} lemma_QuorumIntersection(c:Constants, ds:DistrSys, p1_qrm:set<Packet>, p1_bal:Ballot, p2_qrm:set<Packet>, p2_bal:Ballot)
returns (acc_id:Id)
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
    requires QuorumOfPromiseMsgs(c, ds, p1_qrm, p1_bal)
    requires QuorumOfAcceptMsgs(c, ds, p2_qrm, p2_bal)
    ensures acc_id.agt == Acc && c.ValidAccIdx(acc_id.idx)
    ensures && (exists prom_p : Packet :: prom_p in p1_qrm && prom_p.src == acc_id)
            && (exists acc_p : Packet :: acc_p in p2_qrm && acc_p.src == acc_id)
{
    var p1_src_qrm := extractPacketSources(p1_qrm);
    var p2_src_qrm := extractPacketSources(p2_qrm);
    assert forall id | id in p1_src_qrm :: id in c.acc_ids;
    assert forall id | id in p2_src_qrm :: id in c.acc_ids;

    if forall id | id in c.acc_ids :: !(id in p1_src_qrm && id in p2_src_qrm) {
        assert seqIsUnique(c.acc_ids);
        var acc_ids := setFromSeq(c.acc_ids);
        assert |acc_ids| == 2*c.f+1;
        var e := lemma_Set_Intersection(p1_src_qrm, p2_src_qrm, acc_ids);
        assert e in acc_ids && e in p1_src_qrm && e in p2_src_qrm;
        assert false;
    }
    acc_id :| acc_id in c.acc_ids && acc_id in p1_src_qrm && acc_id in p2_src_qrm;
}


function extractPacketSources(S:set<Packet>) : (res:set<Id>) 
    decreases S
    ensures forall id | id in res :: (exists p :: p in S && p.src == id)
    ensures forall p | p in S :: p.src in res
    ensures UniqueSources(S) ==> |res| == |S|
{ 
    if |S| == 0 then {}
    else 
        var p :| p in S;
        {p.src} + extractPacketSources(S - {p})
}


function setFromSeq(a:seq<Id>) : (res:set<Id>) 
    decreases a
    ensures forall i | 0 <= i < |a| :: a[i] in res
    ensures forall id | id in res :: (exists i :: 0 <= i < |a| && a[i] == id)
    ensures seqIsUnique(a) ==> |a| == |res|
{ 
    if |a| == 0 then {}
    else 
        {a[0]} + setFromSeq(a[1..])
}


lemma lemma_Set_Intersection(S1:set<Id>, S2:set<Id>, U:set<Id>) returns (e:Id)
    requires |S1| > |U|/2
    requires |S2| > |U|/2
    requires forall id | id in S1 :: id in U
    requires forall id | id in S2 :: id in U
    ensures e in U && e in S1 && e in S2
{
    // TODO: assume for now
    assume false;
}

}