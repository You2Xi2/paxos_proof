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
    && LdrAcceptsSetCorrespondToAcceptMsg(c, ds)
    && LdrPromisesSetCorrespondToPromiseMsg(c, ds)
    && AccPromisedBallotLargerThanAccepted(c, ds)
    && AcceptMsgImpliesAccepted(c, ds)
    && PromisedImpliesNoMoreAccepts(c, ds)
    && (forall i | c.ValidLdrIdx(i) && LeaderHasDecided(c, ds, i) 
        :: Agreement_Inv_Decided(c, ds, i)
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


/* If a acceptor acc promised b, then there can be no accept messages in network with 
* ballot b' such that current acc.accepted.b < b'< b */
predicate PromisedImpliesNoMoreAccepts(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i, p | 
        && c.ValidAccIdx(i) 
        && p in ds.network.sentPackets 
        && p.src == Id(Acc, i) 
        && p.msg.Accept?
    ::
        || BalLtEq(ds.acceptors[i].promised, p.msg.bal)
        || BalLtEq(p.msg.bal, ds.acceptors[i].accepted.b)
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
    && QuorumOfCorrespondingAccepts(c, ds, i)
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

predicate QuorumOfCorrespondingAccepts(c:Constants, ds:DistrSys, i:int) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i)
{
    |ds.leaders[i].accepts| == c.f + 1
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
        NextPreservesAgreementInv_SomeoneHadDecided(c, ds, ds');
    } else {
        NextPreservesAgreementInv_NoneHadDecided(c, ds, ds');
    }
}


lemma NextPreservesAgreementInv_SomeoneHadDecided(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires SomeLeaderHasDecided(c, ds)
    ensures Agreement_Inv(c, ds')
{
    var i1 :| c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1);
    var b1, v1 := ds.leaders[i1].ballot, ds.leaders[i1].val;
    var actor, recvIos, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        // If actor is a Leader
        // TODO
        assume false;
        assert Agreement_Inv(c, ds');
    } else {
        // If actor is an Acceptor
        assert Agreement(c, ds');
        assert LdrBallotNotBottom(c, ds');
        assert LdrAcceptsSetCorrespondToAcceptMsg(c, ds');
        assert LdrPromisesSetCorrespondToPromiseMsg(c, ds');
        assert AccPromisedBallotLargerThanAccepted(c, ds'); 
        assert AcceptMsgImpliesAccepted(c, ds');
        assert PromisedImpliesNoMoreAccepts(c, ds');
        
        // Prove Agreement_Inv_Decided properties
        forall i2 | c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds', i2) 
        ensures Agreement_Inv_Decided(c, ds', i2)
        {
            // Note i2 has been decided in ds; it's not a new decision
            assert LeaderHasDecided(c, ds, i2); 
            var b2, v2 := ds.leaders[i2].ballot, ds.leaders[i2].val;
            assert v2 == v1;
            assert LargerBallotPhase2LeadersV(c, ds, v2, b2);
            assert LargerBallotAcceptors(c, ds', v2, b2);
            assert LargerBallotPromiseMsgs(c, ds', v2, b2);
            assert LargerBallotProposeMsgs(c, ds', v2, b2);
            assert QuorumOfCorrespondingAccepts(c, ds', i2);
            assert LargerBallotsPromiseQrms(c, ds', v2, b2);
        }
        assert Agreement_Inv(c, ds');
    }
}

lemma NextPreservesAgreementInv_NoneHadDecided(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires !SomeLeaderHasDecided(c, ds)
    ensures Agreement_Inv(c, ds')
{
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        // If actor is a Leader
        assert Agreement(c, ds');
        assert LdrBallotNotBottom(c, ds');
        assert LdrAcceptsSetCorrespondToAcceptMsg(c, ds');
        assert LdrPromisesSetCorrespondToPromiseMsg(c, ds');
        assert AccPromisedBallotLargerThanAccepted(c, ds'); 
        assert AcceptMsgImpliesAccepted(c, ds');
        assert PromisedImpliesNoMoreAccepts(c, ds');
        
        // Prove Agreement_Inv_Decided properties
        forall i2 | c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds', i2) 
        ensures Agreement_Inv_Decided(c, ds', i2)
        {
            // TODO:
            assume false;
            var b2, v2 := ds.leaders[i2].ballot, ds.leaders[i2].val;
            assert LargerBallotPhase2LeadersV(c, ds, v2, b2);
            assert LargerBallotAcceptors(c, ds', v2, b2);
            assert LargerBallotPromiseMsgs(c, ds', v2, b2);
            assert LargerBallotProposeMsgs(c, ds', v2, b2);
            assert QuorumOfCorrespondingAccepts(c, ds', i2);
            assert LargerBallotsPromiseQrms(c, ds', v2, b2);
        }
        assert Agreement_Inv(c, ds');
    } else {
        // If actor is an Acceptor
        // This case should be trivial
        assert Agreement_Inv(c, ds');
    }
}


}