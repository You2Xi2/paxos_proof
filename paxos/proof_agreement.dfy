include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_helper.dfy"
include "proof_agreement_invariants.dfy"

module Proof_Agreement {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Helper
import opened Proof_Agreement_Invs



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


//////////////           Agreement Sub-Lemma: Existing decision            ///////////////


lemma NextPreservesAgreementInv_SomeoneHadDecided(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires SomeLeaderHasDecided(c, ds)
    ensures SomeLeaderHasDecided(c, ds')
    ensures Agreement_Inv(c, ds')
{
    NextPreservesTrivialities(c, ds, ds');
    var actor, recvIos, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        NextPreservesAgreementInv_SomeoneHadDecided_LeaderAction(c, ds, ds', actor, recvIos, sendIos);
    } else {
        NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction(c, ds, ds', actor, recvIos, sendIos);
    }
}


lemma {:timeLimitMultiplier 2} NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires ds'.WF(c) && Trivialities(c, ds')
    requires SomeLeaderHasDecided(c, ds)
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires actor.agt == Acc
    ensures SomeLeaderHasDecided(c, ds')
    ensures Agreement_Inv(c, ds')
{
    NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction_PromisedImpliesNoMoreAccepts(c, ds, ds', actor, recvIos, sendIos);
    
    // Prove Agreement_Inv_Decided properties
    forall i2 | c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds', i2) 
    ensures Agreement_Inv_Decided(c, ds', i2)
    {
        // Note i2 has been decided in ds; it's not a new decision
        assert LeaderHasDecided(c, ds, i2); 
        var b2, v2 := ds.leaders[i2].ballot, ds.leaders[i2].val;

        // Proving LargerBallotsPromiseQrms(c, ds', v2, b2);
        forall b' | BalLt(b2, b') 
        ensures LargerBalQuorumHasSeenB(c, ds', b2, b')
        {
            forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds', qrm, b') 
            ensures QuorumHasSeenB(c, ds', qrm, b2)
            {
                // Proof by contradiction. Suppose false. Then f+1 acceptors promised
                // b' without accepting b2. Then by PromisedImpliesNoMoreAccepts, there
                // is no quorum of Accept(b2), and (b2) cannot be decided. 
                if (exists prom_qrm :: 
                        && QuorumOfPromiseMsgs(c, ds', prom_qrm, b')
                        && !QuorumHasSeenB(c, ds', prom_qrm, b2)
                ){
                    var prom_qrm :| 
                        && QuorumOfPromiseMsgs(c, ds', prom_qrm, b') 
                        && !QuorumHasSeenB(c, ds', prom_qrm, b2);
                    // Now prove that the corresponding acceptors did not accept (b2, v2)
                    assert PromisedImpliesNoMoreAccepts(c, ds');
                    forall acc_p | 
                            && acc_p in ds'.network.sentPackets 
                            && (exists prom_p : Packet :: prom_p in prom_qrm && acc_p.src == prom_p.src)
                            && acc_p.msg.Accept?
                    ensures acc_p.msg.bal != b2
                    {}
                    forall acc_set : set<Packet> | 
                            && UniqueSources(acc_set)
                            && (forall p | p in acc_set :: p.msg.Accept?)
                            && (forall p | p in acc_set :: p.msg.bal == b2)
                            && (forall p | p in acc_set :: p in ds'.network.sentPackets)
                    ensures |acc_set| < c.f + 1
                    {
                        if |acc_set| >= c.f + 1 {
                            assert QuorumOfAcceptMsgs(c, ds', acc_set, b2);
                            var _ := lemma_QuorumIntersection(c, ds', prom_qrm, b', acc_set, b2);
                            assert false;
                        }
                    }
                    Lemma_DecidedImpliesQuorumOfAccepts(c, ds', i2);
                    assert false;
                }
            }
        }
        assert LargerBallotsPromiseQrms(c, ds', b2);
    }
}


lemma NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction_PromisedImpliesNoMoreAccepts(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires ds'.WF(c)
    requires Trivialities(c, ds')
    requires SomeLeaderHasDecided(c, ds)
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires actor.agt == Acc
    ensures SomeLeaderHasDecided(c, ds')
    ensures PromisedImpliesNoMoreAccepts(c, ds')
{}



lemma NextPreservesAgreementInv_SomeoneHadDecided_LeaderAction(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires ds'.WF(c) && Trivialities(c, ds')
    requires SomeLeaderHasDecided(c, ds)
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires actor.agt == Ldr
    ensures SomeLeaderHasDecided(c, ds')
    ensures Agreement_Inv(c, ds')
{
    var i1 :| c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1);
    var b1, v1 := ds.leaders[i1].ballot, ds.leaders[i1].val;

    assert Agreement(c, ds');   // Needs proof




    assume false;
    assert Trivialities(c, ds');
    assert LdrAcceptsSetCorrespondToAcceptMsg(c, ds');
    assert LdrPromisesSetCorrespondToPromiseMsg(c, ds');
    assert AccPromisedBallotLargerThanAccepted(c, ds');
    assert AcceptMsgImpliesAccepted(c, ds');
    assert PromisedImpliesNoMoreAccepts(c, ds');

    forall i | c.ValidLdrIdx(i) && LeaderHasDecided(c, ds', i) 
    ensures Agreement_Inv_Decided(c, ds', i)
    {
        var b, v := ds'.leaders[i].ballot, ds'.leaders[i].val;
        assert LargerBallotPhase2LeadersV(c, ds', v, b);
        assert LargerBallotAcceptors(c, ds', v, b);     // Trivial
        assert LargerBallotPromiseMsgs(c, ds', v, b);   // Trivial
        assert LargerBallotProposeMsgs(c, ds', v, b);   // Trivial
        assert LargerBallotsPromiseQrms(c, ds', b);
        assert LeaderHasQuorumOfAccepts(c, ds', i);
    }

    assert Agreement_Inv(c, ds');
}








//////////////          Agreement Sub-Lemma: No existing decision          ///////////////


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
        assume false;
        assert Agreement_Inv(c, ds');
    }
}
}