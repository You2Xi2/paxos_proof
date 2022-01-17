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
    // TODO: This is just tedious, so assume for now.
    assume false; 
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Acc {
        assert recvIos[0] in ds.network.sentPackets;
    }

    forall p | p in ds'.network.sentPackets
    ensures ValidPacketSourceDest(c, ds', p)
    {

    }
    assert AllPacketsValid(c, ds');
    assert BallotBottomness_ValueNilness(c, ds');
    
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
        // No values are chosen in this step
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
    requires c.ValidAccId(actor)
    requires !SomeValueChosen(c, ds)
    ensures Agreement_Chosen_Inv(c, ds')
{
    AgreementChosenInv_NoneChosen_AccAction_AgreementChosen(c, ds, ds', actor, recvIos, sendIos);
    assume OneValuePerBallot(c, ds');

    // Leader state
    assume LdrAcceptsSetCorrespondToAcceptMsg(c, ds');      // TODO
    assume LdrPromisesSetCorrespondToPromiseMsg(c, ds');    // TODO

    // Acceptor state
    assume AccPromisedBallotLargerThanAccepted(c, ds');     // TODO

    // Messages
    assume PromiseVBImpliesAcceptMsg(c, ds');               // TODO
    assume AcceptMsgImpliesAccepted(c, ds');                // TODO
    assume AcceptedImpliesAcceptMsg(c, ds');            // TODO
    assume AcceptMsgImpliesProposeMsg(c, ds');              // TODO
    assume LeaderP2ImpliesQuorumOfPromise(c, ds');          // TODO
    assume ProposeMsgImpliesQuorumOfPromise(c, ds');        // TODO
    assume PromisedImpliesNoMoreAccepts(c, ds');            // TODO

    // Chosen
    forall b, v | Chosen(c, ds', b, v) 
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v)
    {
        lemma_NewChosenImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, b, v);
        AgreementChosenInv_NoneChosen_AccAction_NewChosenV(c, ds, ds', actor, recvIos, sendIos, b, v);
    }
    assert Agreement_Chosen_Inv(c, ds');
}


lemma AgreementChosenInv_NoneChosen_AccAction_NewChosenV(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires recvIos[0].msg.Propose?
    requires AcceptorAccept(ds.acceptors[actor.idx], ds'.acceptors[actor.idx], recvIos[0], sendIos);   
    requires !SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    requires OneValuePerBallot(c, ds');
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v)
{
    AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotsPromiseQrms(c, ds, ds', actor, recvIos, sendIos, b, v);
    assert LargerBallotsPromiseQrms(c, ds', b);  

    
    assume LargerBallotAcceptors(c, ds', b, v);     // TODO: we need this
    assume LargerBallotAcceptMsgs(c, ds', b, v);     // TODO: we need this


    // Done
    AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotPromiseMsgs(c, ds, ds', actor, recvIos, sendIos, b, v);
    AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotProposeMsgs(c, ds, ds', actor, recvIos, sendIos, b, v);
    AgreementChosenInv_NoneChosen_AccAction_NewChosenV_P2LeaderV(c, ds, ds', actor, recvIos, sendIos, b, v);
    assert LargerBallotPromiseMsgs(c, ds', b, v);  
    assert LargerBallotProposeMsgs(c, ds', b, v);
    assert LargerBallotPhase2LeadersV(c, ds', b, v);

    assert Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v); 
}


lemma AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotsPromiseQrms(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires recvIos[0].msg.Propose?
    requires AcceptorAccept(ds.acceptors[actor.idx], ds'.acceptors[actor.idx], recvIos[0], sendIos);   
    requires !SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    ensures LargerBallotsPromiseQrms(c, ds', b)
{
    forall b' | BalLt(b, b') 
    ensures LargerBalQuorumHasSeenB(c, ds', b, b')
    {
        forall qrm':set<Packet> | QuorumOfPromiseMsgs(c, ds', qrm', b') 
        ensures QuorumHasSeenB(c, ds', qrm', b){
            AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotsPromiseQrms_helper(c, ds, ds', actor, recvIos, sendIos, b, b', qrm', v);
        }
    }
}

lemma AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotsPromiseQrms_helper(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, b':Ballot, qrm':set<Packet>, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires recvIos[0].msg.Propose?
    requires AcceptorAccept(ds.acceptors[actor.idx], ds'.acceptors[actor.idx], recvIos[0], sendIos);   
    requires !SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    requires BalLt(b, b') 
    requires QuorumOfPromiseMsgs(c, ds', qrm', b')
    ensures QuorumHasSeenB(c, ds', qrm', b)
{
    /* Proof: Suppose otherwise. Then qrm' is in ds, and every Prom in qrm' has promised
    * b', and saw < b. By PromisedImpliesNoMoreAccepts, this means that no Accept(b) messages
    * from any acceptor in qrm'.
    * Call the set of acceptors that chose (b, v) in ds' as qrm. Then qrm and qrm' must be disjoint, 
    * and their union is the set of all acceptors, and qrm is size f. 
    * Now consider the actor taking a step: 
    *   1. If actor is in qrm', it can't accept (b, v). Hence (b,v) not chosen in ds'. C!
    *   2. If actor is in qrm, |qrm| remains f in ds'. C!
    */
    if !QuorumHasSeenB(c, ds', qrm', b) {
        forall prom | prom in qrm' ensures BalLt(prom.msg.vb.b, b) {}
        lemma_NoPromiseSentInAcceptStep(c, ds, ds', actor, recvIos, sendIos);
        assert QuorumOfPromiseMsgs(c, ds, qrm', b');
        
        // Get set of acceptors that promised b' (and not seen b) in ds
        var accs_that_promised := extractPacketSources(qrm');
        assert |accs_that_promised| >= c.f + 1;

        // Get set of acceptors that voted to choose (b, v) in ds
        var qrm :| QuorumOfAcceptMsgs(c, ds', qrm, b) && AccPacketsHaveValueV(qrm, v);
        var new_accept_pkt := lemma_NewChosenImpliesOneNewAcceptPacket(c, ds, ds', actor, recvIos, sendIos, b, v);
        var pre_qrm := qrm - {new_accept_pkt};   // set without the latest Accept from ds->ds' actor.
        assert SetOfAcceptMsgs(c, ds, pre_qrm, b);
        lemma_Set_MinusElem(qrm, new_accept_pkt, |qrm|);
        var accs_that_accepted := extractPacketSources(pre_qrm);
        assert |accs_that_accepted| >= c.f;

        // Show that accs_that_promised && accs_that_accepted are disjoint;
        // use PromisedImpliesNoMoreAccepts
        forall id | id in accs_that_promised 
        ensures id !in accs_that_accepted
        {
            var prom :| prom in qrm' && prom.src == id;
            forall accp | accp in qrm 
            ensures accp.src != id
            {
                if accp.src == id {      
                    assert !BalLtEq(accp.msg.bal, prom.msg.vb.b);
                    lemma_BalLtSynonyms(b, b');
                    assert !BalLtEq(prom.msg.bal, accp.msg.bal);
                    assert false;
                }
            }
        }
        lemma_Set_DisjointSets(accs_that_promised, accs_that_accepted);

        // Consider the current actor taking a step
        lemma_IdSetCover(c, ds, accs_that_promised, accs_that_accepted, actor);
        if actor in accs_that_promised {
            assert BalLtEq(b', ds.acceptors[actor.idx].promised);   // by PromiseMsgImpliesPromised
            lemma_BalLtTransitivity1(b, b', ds.acceptors[actor.idx].promised);
            lemma_NewChosenImpliesIncomingProposalBV(c, ds, ds', actor, recvIos, sendIos, b, v);
            assert !AcceptorAccept(ds.acceptors[actor.idx], ds'.acceptors[actor.idx], recvIos[0], sendIos); 
            assert false;
        } else {
            assert actor in accs_that_accepted;
            var p :| p in pre_qrm && p.src == actor && isAcceptPkt(ds, p) && p.msg.bal == b;
            lemma_NewChosenImpliesIncomingProposalBV(c, ds, ds', actor, recvIos, sendIos, b, v);
            assert sendIos[0] == p;
            assert ds'.network.sentPackets == ds.network.sentPackets;
            assert false;       // violates lemma_NewChosenImpliesOneNewAcceptPacket
        }
    }
}



lemma AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotPromiseMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires !SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    requires LargerBallotAcceptMsgs(c, ds', b, v)
    ensures LargerBallotPromiseMsgs(c, ds', b, v)
{
    forall p | isPromisePkt(ds', p) && BalLtEq(b, p.msg.vb.b)
    ensures p.msg.vb.v == v 
    {
        var b', v' := p.msg.vb.b, p.msg.vb.v;
        var ap :|  && isAcceptPkt(ds', ap)
                    && ap.src == p.src
                    && ap.msg.bal == b'
                    && ap.msg.val == v';
        assert LargerBallotAcceptMsgs(c, ds', b, v);
        if v' != v {
            assert false;
        }
    }
}


lemma AgreementChosenInv_NoneChosen_AccAction_NewChosenV_LargerBallotProposeMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires !SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    requires LargerBallotPromiseMsgs(c, ds', b, v)
    requires LargerBallotsPromiseQrms(c, ds', b)
    ensures LargerBallotProposeMsgs(c, ds', b, v)
{
    forall p | isProposePkt(ds', p) && BalLtEq(b, p.msg.bal)
    ensures p.msg.val == v
    {
        var b', v' := p.msg.bal, p.msg.val;
        if b' == b {
            assert v == v';     // by OneValuePerBallot_ProposeMsg
        } else {
            var prom_qrm :| && QuorumOfPromiseMsgs(c, ds', prom_qrm, b')
                            && (|| PromisePktWithHighestBallot(prom_qrm).msg.vb.v == v'
                                || PromisePktWithHighestBallot(prom_qrm).msg.vb.v == Nil);
            var prom := PromisePktWithHighestBallot(prom_qrm);
            var prom_smaller:Packet :| prom_smaller in prom_qrm && BalLtEq(b, prom_smaller.msg.vb.b);  // because Quorum must have seen b (LargerBallotsPromiseQrms)
            lemma_BalLtEqTransitivity(b, prom_smaller.msg.vb.b, prom.msg.vb.b);
            assert PromisePktWithHighestBallot(prom_qrm).msg.vb.v == v;     // because LargerBallotPromiseMsgs
        }
    }
}


lemma AgreementChosenInv_NoneChosen_AccAction_NewChosenV_P2LeaderV(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires recvIos[0].msg.Propose?
    requires AcceptorAccept(ds.acceptors[actor.idx], ds'.acceptors[actor.idx], recvIos[0], sendIos);   
    requires !SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    requires LargerBallotsPromiseQrms(c, ds', b)
    requires LargerBallotPromiseMsgs(c, ds', b, v)
    ensures LargerBallotPhase2LeadersV(c, ds', b, v)
{
    forall l_idx |  && c.ValidLdrIdx(l_idx) 
                    && BalLtEq(b, ds'.leaders[l_idx].ballot) 
                    && LeaderInPhase2(c, ds', l_idx) 
    ensures LeaderHasValueV(c, ds', l_idx, v)
    {
        if !LeaderHasValueV(c, ds', l_idx, v) {
            var b', v' := ds'.leaders[l_idx].ballot, ds'.leaders[l_idx].val;
            assert v' != v;
            if b' == b {
                var prop_p := lemma_ChosenImpliesProposeMsg(c, ds', b, v);
                assert v == v';
                assert false; 
            } else {
                assert BalLt(b, b');
                var qrm' :| && QuorumOfPromiseMsgs(c, ds', qrm', b')
                            && (|| PromisePktWithHighestBallot(qrm').msg.vb.v == v'
                                || PromisePktWithHighestBallot(qrm').msg.vb.v == Nil);
                if PromisePktWithHighestBallot(qrm').msg.vb.v == Nil {
                    lemma_HighestPromiseValNilImpliesAllBottom(qrm');
                    assert !QuorumHasSeenB(c, ds', qrm', b);
                    assert false;
                } else {
                    var pivot:Packet :| pivot in qrm' && BalLtEq(b, pivot.msg.vb.b);
                    assert pivot.msg.vb.v == v;
                    forall p:Packet | p in qrm' && BalLtEq(pivot.msg.vb.b, p.msg.vb.b) 
                    ensures p.msg.vb.v == v {
                        lemma_BalLtEqTransitivity(b, pivot.msg.vb.b, p.msg.vb.b);
                    }
                    lemma_PromisePktWithHighestBallotProperty(qrm', pivot, v);
                    assert PromisePktWithHighestBallot(qrm').msg.vb.v == v;
                    assert false;
                }
            }
        }
    }
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
    if SomeValueChosen(c, ds') {
        var v, b :| Chosen(c, ds', b, v);
        lemma_NewChosenImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, b, v);
        var a, a' := ds.acceptors[actor.idx], ds'.acceptors[actor.idx];
        assert AcceptorAccept(a, a', recvIos[0], sendIos);
        forall b', v' | Chosen(c, ds', b', v') 
        ensures b' == b && v' == v
        {
            if !(b' == b && v' == v) {
                var qrm' :| && QuorumOfAcceptMsgs(c, ds', qrm', b') 
                            && AccPacketsHaveValueV(qrm', v');
                forall p | p in qrm' 
                ensures p in ds.network.sentPackets
                {
                    if p !in ds.network.sentPackets{
                        lemma_NewPacketsComeFromSendIos(c, ds, ds', actor, recvIos, sendIos);
                        lemma_SingleElemList(sendIos, sendIos[0]);
                        assert false;
                    }
                }
                assert Chosen(c, ds, b', v');
                assert false;
            }
        }
    }
}














//////////////           Agreement Sub-Lemma: Existing decision            ///////////////


lemma AgreementChosenInv_SomeChosen_AccAction_MaybeChoose(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires actor.agt == Acc
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v)
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v)
{
    assume false;
    // forall l_idx | && c.ValidLdrIdx(l_idx) 
    //             && BalLtEq(b, ds'.leaders[l_idx].ballot) 
    //             && LeaderInPhase2(c, ds', l_idx) 
    // ensures LeaderHasValueV(c, ds', l_idx, v)
    // {
    //     if exists l_idx :: 
    //         && c.ValidLdrIdx(l_idx) 
    //         && BalLtEq(b, ds'.leaders[l_idx].ballot) 
    //         && LeaderInPhase2(c, ds', l_idx) 
    //         && !LeaderHasValueV(c, ds', l_idx, v)
    //     {
    //         var l_idx :| c.ValidLdrIdx(l_idx) && BalLtEq(b, ds'.leaders[l_idx].ballot) && LeaderInPhase2(c, ds', l_idx) && !LeaderHasValueV(c, ds', l_idx, v);
    //         assert ds.leaders[l_idx] == ds'.leaders[l_idx];
    //         var b', v' := ds.leaders[l_idx].ballot, ds.leaders[l_idx].val;
    //         var qrm'  :| && QuorumOfPromiseMsgs(c, ds, qrm', b')
    //                     && (|| PromisePktWithHighestBallot(qrm').v == v'
    //                         || PromisePktWithHighestBallot(qrm').v == Nil);
            
    //         assert false;
    //     }
    //     assert LeaderHasValueV(c, ds', l_idx, v);
    // }

    // assert LargerBallotPhase2LeadersV(c, ds', v, b);  //

    // assume false;
    // assert LargerBallotAcceptors(c, ds', v, b);
    // assert LargerBallotPromiseMsgs(c, ds', v, b);
    // assert LargerBallotProposeMsgs(c, ds', v, b);
    // assert LargerBallotsPromiseQrms(c, ds', b);

    // assert Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v); 
}




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