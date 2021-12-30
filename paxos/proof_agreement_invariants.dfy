include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"

module Proof_Agreement_Invs {
import opened Network
import opened Agents
import opened Types
import opened Synod


/* All correct processes decide the same value */
predicate Agreement(c:Constants, ds:DistrSys) 
    requires c.WF()
    requires ds.WF(c)
{
    forall i1, i2 | 
        && c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1) 
        && c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds, i2) 
    :: TwoLeadersHaveSameV(c, ds, i1, i2)
}


/* Only one value can be chosen */
predicate Agreement_Chosen(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
{
    forall b1, b2, v1, v2 | Chosen(c, ds, b1, v1) && Chosen(c, ds, b2, v2)
    :: v1 == v2
}


predicate Trivialities(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && BallotBottomness_ValueNilness(c, ds)
    && AllPacketsValid(c, ds)
}


/* Invariants for establishing Agreement */
predicate Agreement_Chosen_Inv(c:Constants, ds:DistrSys) 
{
    && c.WF()
    && ds.WF(c)
    && Trivialities(c, ds)
    
    && Agreement_Chosen(c, ds)
    && OneValuePerBallot(c, ds)

    // Leader state
    && LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
    && LdrPromisesSetCorrespondToPromiseMsg(c, ds)

    // Acceptor state
    && AccPromisedBallotLargerThanAccepted(c, ds)

    // Messages
    && PromiseVBImpliesAcceptMsg(c, ds)
    && AcceptMsgImpliesAccepted(c, ds)
    && AcceptedImpliesAcceptMessage(c, ds)
    && AcceptMsgImpliesProposeMsg(c, ds)
    && LeaderP2ImpliesQuorumOfPromise(c, ds)
    && ProposeMsgImpliesQuorumOfPromise(c, ds)
    && PromisedImpliesNoMoreAccepts(c, ds)

    // Chosen
    && (forall b, v | Chosen(c, ds, b, v) 
        :: Agreement_Chosen_Inv_SomeValChosen(c, ds, b, v)
    )
}


/* Things that are true if v is chosen with ballot b. */
predicate Agreement_Chosen_Inv_SomeValChosen(c:Constants, ds:DistrSys, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds)
    requires Chosen(c, ds, b, v) 
{
    && LargerBallotPhase2LeadersV(c, ds, v, b)
    && LargerBallotAcceptors(c, ds, v, b)
    && LargerBallotPromiseMsgs(c, ds, v, b)
    && LargerBallotProposeMsgs(c, ds, v, b)
    && LargerBallotsPromiseQrms(c, ds, b)
}


/* Only one value can be associated with each ballot */
predicate OneValuePerBallot(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && OneValuePerBallot_Leaders(c, ds)
    && OneValuePerBallot_ProposeMsg(c, ds)
    && OneValuePerBallot_AcceptMsg(c, ds)
    && OneValuePerBallot_ProposeMsgAndLeader(c, ds)
}

predicate OneValuePerBallot_Leaders(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall l1, l2 | c.ValidLdrIdx(l1) && c.ValidLdrIdx(l2) && l1!=l2 :: ds.leaders[l1].ballot != ds.leaders[l2].ballot
}

predicate OneValuePerBallot_ProposeMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prop_p1, prop_p2 | 
        && prop_p1 in ds.network.sentPackets && prop_p2 in ds.network.sentPackets
        && prop_p1.msg.Propose? && prop_p2.msg.Propose?
        && prop_p1.msg.bal == prop_p2.msg.bal
        :: 
        prop_p1.msg.val == prop_p2.msg.val
}

predicate OneValuePerBallot_AcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall acc_p1, acc_p2 | 
        && acc_p1 in ds.network.sentPackets && acc_p2 in ds.network.sentPackets
        && acc_p1.msg.Accept? && acc_p2.msg.Accept?
        && acc_p1.msg.bal == acc_p2.msg.bal
        :: 
        acc_p1.msg.val == acc_p1.msg.val
}

predicate OneValuePerBallot_ProposeMsgAndLeader(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall l_idx, prop | 
        && c.ValidLdrIdx(l_idx)
        && LeaderInPhase2(c, ds, l_idx) 
        && prop in ds.network.sentPackets
        && prop.msg.Propose?
        && prop.msg.bal == ds.leaders[l_idx].ballot
        :: 
        prop.msg.val == ds.leaders[l_idx].val
}


/* For each promise message p, if it contains an accepted (v, b), then there is an 
* Accept(b) in the network from the same source */
predicate PromiseVBImpliesAcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prom_p | 
        && prom_p in ds.network.sentPackets 
        && prom_p.msg.Promise?
        && prom_p.msg.vb.b != Bottom
    :: 
    (exists acc_p :: 
        && acc_p in ds.network.sentPackets
        && acc_p.msg.Accept?
        && acc_p.src == prom_p.src
        && acc_p.msg.bal == prom_p.msg.vb.b
        && acc_p.msg.val == prom_p.msg.vb.v)
}

/* If an Accept msg in network with src x, ballot b, then balval of acceptor x 
* has has ballot >= b */
predicate AcceptMsgImpliesAccepted(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p | 
        && p in ds.network.sentPackets 
        && p.msg.Accept?
        && c.ValidAccIdx(p.src.idx) 
    ::
        BalLtEq(p.msg.bal, ds.acceptors[p.src.idx].accepted.b)
}

/* If an acceptor has currently accepted ballot b, then there must be an Accept message in the network
* from that acceptor */
predicate AcceptedImpliesAcceptMessage(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall idx | 
        && c.ValidAccIdx(idx) 
        && ds.acceptors[idx].accepted.b != Bottom
    :: (
    exists p ::
        && p in ds.network.sentPackets 
        && p.msg.Accept?
        && p.msg.bal == ds.acceptors[idx].accepted.b
        && p.msg.val == ds.acceptors[idx].accepted.v
        && p.src == Id(Acc, idx)
    )
}

/* For each Accept(b,v) message, there is a corresponding Propose message Propose(b,v) 
* in the network */
predicate AcceptMsgImpliesProposeMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall acc_p | 
        && acc_p in ds.network.sentPackets 
        && acc_p.msg.Accept?
    :: (
    var b, v := acc_p.msg.bal, acc_p.msg.val;
    var ldr := acc_p.dst;
    var acc := acc_p.src;
    exists prop_p :: 
        && prop_p in ds.network.sentPackets
        && prop_p.msg.Propose?
        && prop_p.src == ldr
        && prop_p.dst == acc
        && prop_p.msg.bal == b
        && prop_p.msg.val == v
    )
}


/* For each leader in phase 2, there is a corresponding quorum of Promise packets 
* in the network supporting it's ballot */
predicate LeaderP2ImpliesQuorumOfPromise(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall idx | c.ValidLdrIdx(idx) && LeaderInPhase2(c, ds, idx)
    :: (
    var b := ds.leaders[idx].ballot;
    var v := ds.leaders[idx].val;
    exists qrm  :: 
        && QuorumOfPromiseMsgs(c, ds, qrm, b)
        && (|| PromiseWithHighestBallot(qrm).v == v
            || PromiseWithHighestBallot(qrm).v == Nil
        )
    )
}


/* For each Propose(v, b) message, there is a corresponding quorum of Promise packets 
* in the network */
predicate ProposeMsgImpliesQuorumOfPromise(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall prop_p | 
        && prop_p in ds.network.sentPackets 
        && prop_p.msg.Propose?
    :: (
    var b := prop_p.msg.bal;
    var v := prop_p.msg.val;
    exists qrm  :: 
        && QuorumOfPromiseMsgs(c, ds, qrm, b)
        && (|| PromiseWithHighestBallot(qrm).v == v
            || PromiseWithHighestBallot(qrm).v == Nil
        )
    )
}



/* All l.accepts collected by l came from network */
predicate LdrAcceptsSetCorrespondToAcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) ::(
        forall s | s in ds.leaders[i].accepts
        :: Packet(s, Id(Ldr, i), Accept(ds.leaders[i].ballot, ds.leaders[i].val)) in ds.network.sentPackets
    )
}

/* All l.promises collected by l came from network */
predicate LdrPromisesSetCorrespondToPromiseMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) ::(
        forall p | p in ds.leaders[i].promises
        :: p in ds.network.sentPackets
    )
}

/* Acceptor promised ballot always at least as large as accepted ballot */
predicate AccPromisedBallotLargerThanAccepted(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidAccIdx(i) 
    :: BalLtEq(ds.acceptors[i].accepted.b, ds.acceptors[i].promised)
}


/* If a promised packet promised b', with previously accepted (v, b), then 
*   - there can be no accept messages in network, from the same acceptor, 
*       with ballot x such that b < x < b' 
*   - the acceptor either has (v, b) accepted, or accepted some ballot >= b'
*/
predicate PromisedImpliesNoMoreAccepts(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires AllPacketsValid(c, ds) 
{
    forall prom_p | 
        && prom_p in ds.network.sentPackets 
        && prom_p.msg.Promise?
    :: 
    var p1_promised_bal := prom_p.msg.bal;
    var p1_accepted_bal := prom_p.msg.vb.b;
    && AcceptorConstraint(c, ds, prom_p.src, p1_promised_bal, p1_accepted_bal)
    && AcceptMessageConstraint(c, ds, prom_p.src, p1_promised_bal, p1_accepted_bal)
}

predicate AcceptorConstraint(c:Constants, ds:DistrSys, src:Id, p1_promised_bal:Ballot, p1_accepted_bal:Ballot) 
    requires c.WF() && ds.WF(c)
    requires src.agt == Acc && c.ValidAccIdx(src.idx)
{
    var acc := ds.acceptors[src.idx];
    && BalLtEq(p1_promised_bal, acc.promised)
    && (|| acc.accepted.b == p1_accepted_bal
        || BalLtEq(p1_promised_bal, acc.accepted.b)
    )
}

predicate AcceptMessageConstraint(c:Constants, ds:DistrSys, src:Id, p1_promised_bal:Ballot, p1_accepted_bal:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall acc_p | 
        && acc_p in ds.network.sentPackets 
        && acc_p.src == src
        && acc_p.msg.Accept?
    :: 
        || BalLtEq(acc_p.msg.bal, p1_accepted_bal)
        || BalLtEq(p1_promised_bal, acc_p.msg.bal)
}



predicate BallotBottomness_ValueNilness(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && BallotBottomness_ValueNilness_Packets(c, ds)
    && BallotBottomness_ValueNilness_Agents(c, ds)
}

predicate BallotBottomness_ValueNilness_Packets(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p ::
    if isPreparePkt(ds, p) then p.msg.bal != Bottom
    else if isPromisePkt(ds, p) then p.msg.vb.v == Nil <==> p.msg.vb.b == Bottom
    else if isAcceptPkt(ds, p) then p.msg.val != Nil && p.msg.bal != Bottom
    else if isProposePkt(ds, p) then p.msg.val != Nil && p.msg.bal != Bottom
    else true
}

predicate BallotBottomness_ValueNilness_Agents(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && (forall l | l in ds.leaders :: l.ballot != Bottom && l.val != Nil)
    && (forall a | a in ds.acceptors :: a.accepted.b == Bottom <==> a.accepted.v == Nil)
}



/* If v is chosen with ballot b, then all phase 2 leaders with ballots
* b' >= b must be of v */
predicate LargerBallotPhase2LeadersV(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall i' | 
        && c.ValidLdrIdx(i') 
        && BalLtEq(b, ds.leaders[i'].ballot) 
        && LeaderInPhase2(c, ds, i') 
    :: LeaderHasValueV(c, ds, i', v)
}

/* If v is chosen with ballot b, then for any acceptor that accepted a ballot b'>=b, 
* the accepted value is v */
predicate LargerBallotAcceptors(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall i' | c.ValidAccIdx(i') && BalLtEq(b, ds.acceptors[i'].accepted.b)
    :: AcceptorHasValueV(c, ds, i', v)
}


/* If v is chosen with ballot b, then for any Promise msgs with valbal ballot b'>=b, 
* the valbal value is v */
predicate LargerBallotPromiseMsgs(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets && p.msg.Promise? && BalLtEq(b, p.msg.vb.b)
    :: p.msg.vb.v == v
}

/* If v is chosen with ballot b, then for any Propose msgs with ballot b'>=b, 
* the value is v */
predicate LargerBallotProposeMsgs(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets && p.msg.Propose? && BalLtEq(b, p.msg.bal)
    :: p.msg.val == v
}

/* If v is chosen with ballot b, then all Promise quorums for ballots
* b' >= b must come from an acceptor that accepted (v, b) */
predicate LargerBallotsPromiseQrms(c:Constants, ds:DistrSys, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall b' | BalLt(b, b') 
    :: LargerBalQuorumHasSeenB(c, ds, b, b')
}

predicate LargerBalQuorumHasSeenB(c:Constants, ds:DistrSys, b:Ballot, b':Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds, qrm, b') 
    :: QuorumHasSeenB(c, ds, qrm, b)
}

predicate QuorumHasSeenB(c:Constants, ds:DistrSys, qrm:set<Packet>, b:Ballot) 
    requires c.WF() && ds.WF(c)
    requires forall p | p in qrm :: p.msg.Promise?
{
    exists p :: p in qrm && BalLtEq(b, p.msg.vb.b)
}

// predicate LeaderHasQuorumOfAccepts(c:Constants, ds:DistrSys, i:int) 
//     requires c.WF() && ds.WF(c)
//     requires c.ValidLdrIdx(i)
// {
//     |ds.leaders[i].accepts| == c.f + 1
// }

}