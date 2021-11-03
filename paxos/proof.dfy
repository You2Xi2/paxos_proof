include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"

module Proof {
import opened Network
import opened Agents
import opened Types
import opened Synod


/*****************************************************************************************
*                                       Validity                                         *
*****************************************************************************************/

/* If all processes propose v, then every process that decides a value decides v */
predicate Validity(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> AllDecidedProcessesDecidesV(c, ds, v)
}

predicate AllProcessesInitV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: c.ldr_vals[i] == v
}

predicate AllDecidedProcessesDecidesV(c:Constants, ds:DistrSys, v:Value)
    requires c.WF()
    requires ds.WF(c)
{
    forall l | l in ds.leaders && l.state == Decided :: l.val == v
}


/* Invariants for establishing Validity */
predicate Validity_Inv(c:Constants, ds:DistrSys, v:Value) 
{
    && c.WF()
    && ds.WF(c)
    && Validity(c, ds, v)
    && Validity_Inv_AllLdrProposeV(c, ds, v)
    && Validity_Inv_AllAccAcceptsV(c, ds, v)
    && Validity_Inv_AllMessegesContainV(c, ds, v)
}

predicate Validity_Inv_AllMessegesContainV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> forall pkt | pkt in ds.network.sentPackets :: MessageContainsV(pkt.msg, v)
}

predicate MessageContainsV(m: Message, v:Value) {
    match m {
        case Prepare(bal) => true
        case Promise(bal, vb) => vb.v != v ==> vb.v == Nil
        case Propose(bal, val) => val == v
        case Accept(bal) =>  true
        case Preempt(bal) => true
    }
}

predicate Validity_Inv_AllAccAcceptsV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> forall i | c.ValidAccIdx(i) :: ds.acceptors[i].accepted.v != v ==> ds.acceptors[i].accepted.v == Nil 
}

predicate Validity_Inv_AllLdrProposeV(c:Constants, ds:DistrSys, v:Value)
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> 
    && (forall i | c.ValidLdrIdx(i) :: ds.leaders[i].val == v)
    && (forall i | c.ValidLdrIdx(i) :: 
            forall p | p in ds.leaders[i].promises  && p.msg.Promise?
            :: p.msg.vb.v != Nil ==> p.msg.vb.v == v)
}


/* Init ==> Validity_Inv */
lemma InitImpliesValidityInv(c:Constants, ds:DistrSys, v:Value) 
    requires Init(c, ds)
    ensures Validity_Inv(c, ds, v)
{}


/* Validity_Inv && Next ==> Validity_Inv' */
lemma NextPreservesVakidityInv(c:Constants, v:Value, ds:DistrSys, ds':DistrSys) 
    requires Validity_Inv(c, ds, v)
    requires Next(c, ds, ds')
    ensures Validity_Inv(c, ds', v)
{}


/*****************************************************************************************
*                                      Agreement                                         *
*****************************************************************************************/

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
    && LdrBallotNotBottom(c, ds)
    && LdrAcceptsSetUnique(c, ds)
    && LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
    && LdrPromisesSetUnique(c, ds)
    && LdrPromisesSetCorrespondToPromiseMsg(c, ds)
    && (forall i | c.ValidLdrIdx(i) && LeaderHasDecided(c, ds, i) 
        :: Agreement_Inv_Decided(c, ds, i)
    )
}

/* All l.accepts collected by l are unique source */
predicate LdrAcceptsSetUnique(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) ::(
        forall s1, s2 | s1 in ds.leaders[i].accepts && s2 in ds.leaders[i].accepts 
        :: s1 != s2
    )
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

/* All l.promises collected by l are unique source */
predicate LdrPromisesSetUnique(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) ::(
        forall p1, p2 | p1 in ds.leaders[i].promises && p2 in ds.leaders[i].promises 
        :: p1.src != p2.src
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

predicate LdrBallotNotBottom(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && (forall l | l in ds.leaders :: l.ballot != Bottom)
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
    && LargerBallotsPromiseQrms(c, ds, v, b)
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
predicate LargerBallotsPromiseQrms(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall b' | BalLtEq(b, b') 
    :: (forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds, qrm, b') 
        :: exists p :: p in qrm && BalLtEq(b, p.msg.vb.b) 
    )
}



/* Init ==> Agreement_Inv */
lemma InitImpliesAgreementInv(c:Constants, ds:DistrSys) 
    requires Init(c, ds)
    ensures Agreement_Inv(c, ds)
{}


/* Agreement_Inv && Next ==> Agreement_Inv' */
lemma NextPreservesAgreementInv(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    ensures Agreement_Inv(c, ds')
{
    if SomeLeaderHasDecided(c, ds) {
        var i1 :| c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1);
        // TODO
        assume false;
        assert Agreement_Inv(c, ds');
    } else {
        // TODO
        assume false;
        assert Agreement_Inv(c, ds');
    }
}

}