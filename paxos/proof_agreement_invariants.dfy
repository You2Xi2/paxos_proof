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

/* Invariants for establishing Agreement */
predicate Agreement_Inv(c:Constants, ds:DistrSys) 
{
    && c.WF()
    && ds.WF(c)
    && Agreement(c, ds)
    && Trivialities(c, ds)
    && LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
    && LdrPromisesSetCorrespondToPromiseMsg(c, ds)
    && AccPromisedBallotLargerThanAccepted(c, ds)
    && AcceptMsgImpliesAccepted(c, ds)
    && PromisedImpliesNoMoreAccepts(c, ds)
    && (forall i | c.ValidLdrIdx(i) && LeaderHasDecided(c, ds, i) 
        :: Agreement_Inv_Decided(c, ds, i)
    )
}


/* Things that are true if v is decided with ballot b. */
predicate Agreement_Inv_Decided(c:Constants, ds:DistrSys, i:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i) && LeaderHasDecided(c, ds, i) 
{
    var b, v := ds.leaders[i].ballot, ds.leaders[i].val;
    && LargerBallotPhase2LeadersV(c, ds, v, b)
    && LargerBallotAcceptors(c, ds, v, b)
    && LargerBallotPromiseMsgs(c, ds, v, b)
    && LargerBallotProposeMsgs(c, ds, v, b)
    && LargerBallotsPromiseQrms(c, ds, b)
    && LeaderHasQuorumOfAccepts(c, ds, i)
}


predicate Trivialities(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && LdrBallotNotBottom(c, ds)
    && AllPacketsValid(c, ds)
}




/* All l.accepts collected by l came from network */
predicate LdrAcceptsSetCorrespondToAcceptMsg(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) ::(
        forall s | s in ds.leaders[i].accepts
        :: Packet(s, Id(Ldr, i), Accept(ds.leaders[i].ballot)) in ds.network.sentPackets
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

predicate LdrBallotNotBottom(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && (forall l | l in ds.leaders :: l.ballot != Bottom)
}



/* If v is decided with ballot b, then all phase 2 leaders with ballots
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

/* If v is decided with ballot b, then for any acceptor that accepted a ballot b'>=b, 
* the accepted value is v */
predicate LargerBallotAcceptors(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall i' | c.ValidAccIdx(i') && BalLtEq(b, ds.acceptors[i'].accepted.b)
    :: AcceptorHasValueV(c, ds, i', v)
}


/* If v is decided with ballot b, then for any Promise msgs with valbal ballot b'>=b, 
* the valbal value is v */
predicate LargerBallotPromiseMsgs(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets && p.msg.Promise? && BalLtEq(b, p.msg.vb.b)
    :: p.msg.vb.v == v
}

/* If v is decided with ballot b, then for any Propose msgs with ballot b'>=b, 
* the value is v */
predicate LargerBallotProposeMsgs(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets && p.msg.Propose? && BalLtEq(b, p.msg.bal)
    :: p.msg.val == v
}

/* If v is decided with ballot b, then all Promise quorums for ballots
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

predicate LeaderHasQuorumOfAccepts(c:Constants, ds:DistrSys, i:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i)
{
    |ds.leaders[i].accepts| == c.f + 1
}

}