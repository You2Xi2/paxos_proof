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


predicate Trivialities(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && LdrBallotNotBottom(c, ds)
    && AllPacketsValid(c, ds)
}

predicate AllPacketsValid(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets
    :: ValidPacketSourceDest(c, ds, p)
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


/* If a promised packet promised b', with previously accepted (v, b), then there can be no 
* accept messages in network, from the same acceptor, with ballot x 
* such that b < x < b' */
predicate PromisedImpliesNoMoreAccepts(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i, prom_p | 
        && prom_p in ds.network.sentPackets 
        && prom_p.src == Id(Acc, i) 
        && prom_p.msg.Promise?
    :: 
    var b' := prom_p.msg.bal;
    var b := prom_p.msg.vb.b;
    (forall acc_p | 
        && acc_p in ds.network.sentPackets 
        && acc_p.src == Id(Acc, i)
        && prom_p.msg.Accept?
    :: 
        || BalLtEq(acc_p.msg.bal, b)
        || BalLtEq(b', acc_p.msg.bal)
    )
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
    && LargerBallotsPromiseQrms(c, ds, b)
    && LeaderHasQuorumOfAccepts(c, ds, i)
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
    forall b' | BalLtEq(b, b') 
    :: EveryLargerBalQuorumHasSeenB(c, ds, b, b')
}

predicate EveryLargerBalQuorumHasSeenB(c:Constants, ds:DistrSys, b:Ballot, b':Ballot) 
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
    NextPreservesTrivialities(c, ds, ds');
    if SomeLeaderHasDecided(c, ds) {
        NextPreservesAgreementInv_SomeoneHadDecided(c, ds, ds');
    } else {
        NextPreservesAgreementInv_NoneHadDecided(c, ds, ds');
    }
}


lemma NextPreservesTrivialities(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires Trivialities(c, ds)
    ensures Trivialities(c, ds')
{

    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Acc {
        assert recvIos[0] in ds.network.sentPackets;
    }
}


lemma NextPreservesAgreementInv_SomeoneHadDecided(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires Trivialities(c, ds')
    requires SomeLeaderHasDecided(c, ds)
    ensures SomeLeaderHasDecided(c, ds')
    ensures Agreement_Inv(c, ds')
{
    NextPreservesTrivialities(c, ds, ds');
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
        assert Trivialities(c, ds');
        
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
            assert LeaderHasQuorumOfAccepts(c, ds', i2);

            // Proving LargerBallotsPromiseQrms(c, ds', v2, b2);
            forall b' | BalLtEq(b2, b') 
            ensures EveryLargerBalQuorumHasSeenB(c, ds', b2, b')
            {
                forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds', qrm, b') 
                ensures QuorumHasSeenB(c, ds', qrm, b2)
                {
                    // Proof by contradiction. Suppose false. Then f+1 acceptors promised
                    // b' without accepting b2. Then by PromisedImpliesNoMoreAccepts, there
                    // is no quorum of Accept(b2), and (b2) cannot be decided. 
                    if (exists qrm :: 
                            && QuorumOfPromiseMsgs(c, ds', qrm, b')
                            && !QuorumHasSeenB(c, ds', qrm, b2)
                    ){
                        var qrm :| 
                            && QuorumOfPromiseMsgs(c, ds', qrm, b') 
                            && !QuorumHasSeenB(c, ds', qrm, b2);
                        // No Promise packet in this b' quorum has seem b2, which is already decided
                        assert (forall p:Packet | p in qrm :: BalLt(p.msg.vb.b, b2));

                        // Now prove that the corresponding acceptors did not accept (b2, v2)

                        assert PromisedImpliesNoMoreAccepts(c, ds');
                        // forall i, p | 
                        //     && c.ValidAccIdx(i) 
                        //     && p in ds'.network.sentPackets 
                        //     && p.src == Id(Acc, i) 
                        //     && p.msg.Accept?
                        // ::
                        //     || BalLtEq(ds.acceptors[i].promised, p.msg.bal)
                        //     || BalLtEq(p.msg.bal, ds.acceptors[i].accepted.b)

                        // assume false;
                        Lemma_DecidedImpliesQuorumOfAccepts(c, ds', i2);
                        assert false;
                    }
                }
            }
            assert LargerBallotsPromiseQrms(c, ds', b2);
        }
        assert Agreement_Inv(c, ds');
    }
}


lemma NextPreservesAgreementInv_NoneHadDecided(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires Trivialities(c, ds')
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
        assert Trivialities(c, ds');
        
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
            assert LeaderHasQuorumOfAccepts(c, ds', i2);
            assert LargerBallotsPromiseQrms(c, ds', b2);
        }
        assert Agreement_Inv(c, ds');
    } else {
        // If actor is an Acceptor
        // This case should be trivial
        assert Agreement_Inv(c, ds');
    }
}




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

}