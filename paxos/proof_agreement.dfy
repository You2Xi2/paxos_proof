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



/* Init ==> Agreement_Chosen_Inv */
lemma InitImpliesAgreementChosenInv(c:Constants, ds:DistrSys) 
    requires Init(c, ds)
    ensures Agreement_Chosen_Inv(c, ds)
{}


lemma NextPreservesTrivialities(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires Next(c, ds, ds')
    requires Trivialities(c, ds)
    ensures Trivialities(c, ds')
{

    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Acc {
        assert recvIos[0] in ds.network.sentPackets;
    }
}


/* Agreement_Chosen_Inv && Next ==> Agreement_Chosen_Inv' */
lemma NextPreservesAgreementChosenInv(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires Next(c, ds, ds')
    ensures Agreement_Chosen_Inv(c, ds')
{
    NextPreservesTrivialities(c, ds, ds');
    if SomeValueChosen(c, ds) {
        // TODO
        assume false;
    } else {
        // TODO
        AgreementChosenInv_NoneChosen(c, ds, ds');
    }
}

// //////////////          Agreement Sub-Lemma: No existing decision          ///////////////


lemma AgreementChosenInv_NoneChosen(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires !SomeValueChosen(c, ds)
    ensures Agreement_Chosen_Inv(c, ds')
{
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        // If actor is a Leader
        assume false;
        assert Agreement_Chosen_Inv(c, ds');
    } else {
        // If actor is an Acceptor: This is the tricky case as 
        // some value may be chosen in this step
        AgreementChosenInv_NoneChosen_AccAction(c, ds, ds', actor, recvIos, sendIos);
    }
}


lemma AgreementChosenInv_NoneChosen_AccAction(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires actor.agt == Acc
    requires !SomeValueChosen(c, ds)
    ensures Agreement_Chosen_Inv(c, ds')
{
    AgreementChosenInv_NoneChosen_AccAction_AgreementChosen(c, ds, ds', actor, recvIos, sendIos);

    assume false;
    assert OneValuePerBallot(c, ds');

    // Leader state
    assert LdrAcceptsSetCorrespondToAcceptMsg(c, ds');
    assert LdrPromisesSetCorrespondToPromiseMsg(c, ds');

    // Acceptor state
    assert AccPromisedBallotLargerThanAccepted(c, ds');

    // Messages
    assert PromiseVBImpliesAcceptMsg(c, ds');
    assert AcceptMsgImpliesAccepted(c, ds');
    assert AcceptedImpliesAcceptMessage(c, ds');
    assert AcceptMsgImpliesProposeMsg(c, ds');
    assert ProposeMsgImpliesQuorumOfPromise(c, ds');
    assert PromisedImpliesNoMoreAccepts(c, ds');

    // Chosen
    forall b, v | Chosen(c, ds', b, v) 
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v)
    {
        assume false;
        assert Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v); //
    }
    assert Agreement_Chosen_Inv(c, ds');
}



lemma AgreementChosenInv_NoneChosen_AccAction_AgreementChosen(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires actor.agt == Acc
    requires !SomeValueChosen(c, ds)
    ensures Agreement_Chosen(c, ds')
{
    // At most one value can be chosen in ds'.
    if recvIos[0].msg.Propose? {
        var a, a' := ds.acceptors[actor.idx], ds'.acceptors[actor.idx];
        if BalLtEq(a.promised, recvIos[0].msg.bal) {
            var b, v := recvIos[0].msg.bal, recvIos[0].msg.val;
            forall b', v' | Chosen(c, ds', b', v') 
            ensures b' == b && v' == v
            {
                if !(b' == b && v' == v) {
                    assert Chosen(c, ds, b', v');
                    assert false;
                }
            }
        } else {
            assert forall p:Packet | p in ds'.network.sentPackets && p.msg.Accept? :: p in ds.network.sentPackets;
            if exists b, v :: Chosen(c, ds', b, v) { 
                lemma_NoNewAcceptsImpliesNoNewChosen(c, ds, ds');
                assert false;
            }
        }
    } else {
        // No new Accept packets generated in this step, so nothing is chosen in ds'
        assert forall p:Packet | p in ds'.network.sentPackets && p.msg.Accept? :: p in ds.network.sentPackets;
        if exists b, v :: Chosen(c, ds', b, v) { 
            lemma_NoNewAcceptsImpliesNoNewChosen(c, ds, ds');
            assert false;
        }
    }
}














//////////////           Agreement Sub-Lemma: Existing decision            ///////////////


// lemma NextPreservesAgreementInv_SomeoneHadDecided(c:Constants, ds:DistrSys, ds':DistrSys) 
//     requires Agreement_Chosen_Inv(c, ds)
//     requires Next(c, ds, ds')
//     requires SomeLeaderHasDecided(c, ds)
//     ensures SomeLeaderHasDecided(c, ds')
//     ensures Agreement_Chosen_Inv(c, ds')
// {
//     NextPreservesTrivialities(c, ds, ds');
//     var actor, recvIos, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
//     if actor.agt == Ldr {
//         NextPreservesAgreementInv_SomeoneHadDecided_LeaderAction(c, ds, ds', actor, recvIos, sendIos);
//     } else {
//         NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction(c, ds, ds', actor, recvIos, sendIos);
//     }
// }


// lemma {:timeLimitMultiplier 2} NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
//     requires Agreement_Chosen_Inv(c, ds)
//     requires Next(c, ds, ds')
//     requires ds'.WF(c) && Trivialities(c, ds')
//     requires SomeLeaderHasDecided(c, ds)
//     requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
//     requires actor.agt == Acc
//     ensures SomeLeaderHasDecided(c, ds')
//     ensures Agreement_Chosen_Inv(c, ds')
// {
//     NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction_PromisedImpliesNoMoreAccepts(c, ds, ds', actor, recvIos, sendIos);
    
//     // Prove Agreement_Inv_Decided properties
//     forall i2 | c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds', i2) 
//     ensures Agreement_Inv_Decided(c, ds', i2)
//     {
//         // Note i2 has been decided in ds; it's not a new decision
//         assert LeaderHasDecided(c, ds, i2); 
//         var b2, v2 := ds.leaders[i2].ballot, ds.leaders[i2].val;

//         // Proving LargerBallotsPromiseQrms(c, ds', v2, b2);
//         forall b' | BalLt(b2, b') 
//         ensures LargerBalQuorumHasSeenB(c, ds', b2, b')
//         {
//             forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds', qrm, b') 
//             ensures QuorumHasSeenB(c, ds', qrm, b2)
//             {
//                 // Proof by contradiction. Suppose false. Then f+1 acceptors promised
//                 // b' without accepting b2. Then by PromisedImpliesNoMoreAccepts, there
//                 // is no quorum of Accept(b2), and (b2) cannot be decided. 
//                 if (exists prom_qrm :: 
//                         && QuorumOfPromiseMsgs(c, ds', prom_qrm, b')
//                         && !QuorumHasSeenB(c, ds', prom_qrm, b2)
//                 ){
//                     var prom_qrm :| 
//                         && QuorumOfPromiseMsgs(c, ds', prom_qrm, b') 
//                         && !QuorumHasSeenB(c, ds', prom_qrm, b2);
//                     // Now prove that the corresponding acceptors did not accept (b2, v2)
//                     assert PromisedImpliesNoMoreAccepts(c, ds');
//                     forall acc_p | 
//                             && acc_p in ds'.network.sentPackets 
//                             && (exists prom_p : Packet :: prom_p in prom_qrm && acc_p.src == prom_p.src)
//                             && acc_p.msg.Accept?
//                     ensures acc_p.msg.bal != b2
//                     {}
//                     forall acc_set : set<Packet> | 
//                             && UniqueSources(acc_set)
//                             && (forall p | p in acc_set :: p.msg.Accept?)
//                             && (forall p | p in acc_set :: p.msg.bal == b2)
//                             && (forall p | p in acc_set :: p in ds'.network.sentPackets)
//                     ensures |acc_set| < c.f + 1
//                     {
//                         if |acc_set| >= c.f + 1 {
//                             assert QuorumOfAcceptMsgs(c, ds', acc_set, b2);
//                             var _ := lemma_QuorumIntersection(c, ds', prom_qrm, b', acc_set, b2);
//                             assert false;
//                         }
//                     }
//                     Lemma_DecidedImpliesQuorumOfAccepts(c, ds', i2);
//                     assert false;
//                 }
//             }
//         }
//         assert LargerBallotsPromiseQrms(c, ds', b2);
//     }
// }


// lemma NextPreservesAgreementInv_SomeoneHadDecided_AcceptorAction_PromisedImpliesNoMoreAccepts(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
//     requires Agreement_Chosen_Inv(c, ds)
//     requires Next(c, ds, ds')
//     requires ds'.WF(c)
//     requires Trivialities(c, ds')
//     requires SomeLeaderHasDecided(c, ds)
//     requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
//     requires actor.agt == Acc
//     ensures SomeLeaderHasDecided(c, ds')
//     ensures PromisedImpliesNoMoreAccepts(c, ds')
// {}


// lemma NextPreservesAgreementInv_SomeoneHadDecided_LeaderAction(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
//     requires Agreement_Chosen_Inv(c, ds)
//     requires Next(c, ds, ds')
//     requires ds'.WF(c) && Trivialities(c, ds')
//     requires SomeLeaderHasDecided(c, ds)
//     requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
//     requires actor.agt == Ldr
//     ensures SomeLeaderHasDecided(c, ds')
//     ensures Agreement_Chosen_Inv(c, ds')
// {
//     var i1 :| c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1);
//     var b1, v1 := ds.leaders[i1].ballot, ds.leaders[i1].val;

//     forall i | c.ValidLdrIdx(i) && LeaderHasDecided(c, ds', i) 
//     ensures Agreement_Inv_Decided(c, ds', i)
//     {
//          // TODO
//         assume false;
//         var b, v := ds'.leaders[i].ballot, ds'.leaders[i].val;
//         assert LargerBallotPhase2LeadersV(c, ds', v, b);
//         assert LargerBallotAcceptors(c, ds', v, b);     // Trivial
//         assert LargerBallotPromiseMsgs(c, ds', v, b);   // Trivial
//         assert LargerBallotProposeMsgs(c, ds', v, b);   // Trivial
//         assert LargerBallotsPromiseQrms(c, ds', b);
//         assert LeaderHasQuorumOfAccepts(c, ds', i);
//     }
//     NextPreservesAgreementInv_SomeoneHadDecided_LeaderAction_Agreement(c, ds, ds', actor, recvIos, sendIos);
//     assert Trivialities(c, ds');
//     assert LdrAcceptsSetCorrespondToAcceptMsg(c, ds');
//     assert LdrPromisesSetCorrespondToPromiseMsg(c, ds');
//     assert AccPromisedBallotLargerThanAccepted(c, ds');
//     assert AcceptMsgImpliesAccepted(c, ds');
//     assert PromisedImpliesNoMoreAccepts(c, ds');
//     assert Agreement_Chosen_Inv(c, ds');
// }


// lemma NextPreservesAgreementInv_SomeoneHadDecided_LeaderAction_Agreement(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
//     requires Agreement_Chosen_Inv(c, ds)
//     requires Next(c, ds, ds')
//     requires ds'.WF(c) && Trivialities(c, ds')
//     requires SomeLeaderHasDecided(c, ds)
//     requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
//     requires actor.agt == Ldr
//     ensures SomeLeaderHasDecided(c, ds')
//     ensures Agreement(c, ds')
// {
//     var i1 :| c.ValidLdrIdx(i1) && LeaderHasDecided(c, ds, i1);
//     var b1, v1 := ds.leaders[i1].ballot, ds.leaders[i1].val;

//     forall i2 | i2 != i1 && c.ValidLdrIdx(i2) && LeaderHasDecided(c, ds', i2) 
//     ensures TwoLeadersHaveSameV(c, ds', i1, i2) 
//     {
//         var b2, v2 := ds.leaders[i2].ballot, ds.leaders[i2].val;
//         if actor.agt == Ldr {
//             if actor.idx == i2 {
//                 if !LeaderHasDecided(c, ds, i2) {
//                     // This is where the heavy lifting is
//                     assert LeaderInPhase2(c, ds, i2);
//                     if BalLtEq(b1, b2) {
//                         assert LeaderHasValueV(c, ds, i2, v1);
//                         assert LeaderHasValueV(c, ds', i2, v1);
//                     } else {
//                         // TODO
//                         assume false;

//                         assert LargerBallotPhase2LeadersV(c, ds', v2, b2);
//                         assert BalLtEq(b2, b1);
//                         assert LeaderHasValueV(c, ds', i1, v2);
//                     }
//                 } else {
//                     assert TwoLeadersHaveSameV(c, ds', i1, i2);
//                 }
//             } else {
//                 assert LeaderHasDecided(c, ds, i2);
//                 assert TwoLeadersHaveSameV(c, ds', i1, i2);
//             }
//         } else { 
//             assert TwoLeadersHaveSameV(c, ds', i1, i2);
//         }
//     }
//     assert Agreement(c, ds');   
// }


}