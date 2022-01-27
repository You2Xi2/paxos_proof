include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_helper.dfy"
include "proof_axioms.dfy"
include "proof_agreement_invariants.dfy"
include "proof_agreement_chosenProperties1.dfy"

module Proof_Agreement_ChosenProperties_2 {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Helper
import opened Proof_Axioms
import opened Proof_Agreement_Invs
import opened Proof_Agreement_ChosenProperties_1



/////////////////       Agreement Sub-Lemma: Some existing decision        ///////////////

lemma AgreementChosenInv_SomeChosen(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires SomeValueChosen(c, ds)
    ensures Agreement_Chosen_Inv_ChosenProperties(c, ds')
{
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        // If actor is a Leader
        AgreementChosenInv_SomeChosen_LdrAction(c, ds, ds', actor, recvIos, sendIos);
    } else {
        // If actor is Acceptor
        AgreementChosenInv_SomeChosen_AccAction(c, ds, ds', actor, recvIos, sendIos);
    }
}


lemma AgreementChosenInv_SomeChosen_AccAction(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires SomeValueChosen(c, ds)
    ensures Agreement_Chosen_Inv_ChosenProperties(c, ds')
{
    forall b', v' | Chosen(c, ds', b', v') 
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b', v')
    {
        if Chosen(c, ds, b', v') {
            assume false;
        } else {
            // var b, v :| Chosen(c, ds, b, v);
            lemma_NewChosenImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, b', v');
            assume LargerBallotsPromiseQrms(c, ds', b');    // TODO
            assume LargerBallotAcceptMsgs(c, ds', b', v');  // TODO

            AgreementChosenInv_SomeChosen_AccAction_LargerBallotAcceptors(c, ds, ds', actor, recvIos, sendIos, b', v');
            AgreementChosenInv_SomeChosen_AccAction_LargerBallotPromiseMsgs(c, ds, ds', actor, recvIos, sendIos, b', v');
            AgreementChosenInv_SomeChosen_AccAction_LargerBallotProposeMsgs(c, ds, ds', actor, recvIos, sendIos, b', v');
            AgreementChosenInv_SomeChosen_AccAction_LargerBallotPhase2LeadersV(c, ds, ds', actor, recvIos, sendIos, b', v');
            assert LargerBallotAcceptors(c, ds', b', v');
            assert LargerBallotPromiseMsgs(c, ds', b', v');
            assert LargerBallotProposeMsgs(c, ds', b', v');
            assert LargerBallotPhase2LeadersV(c, ds', b', v');

            assume SameBallotLeaderNotInPhase1(c, ds', b');
        }
    }
}


lemma AgreementChosenInv_SomeChosen_AccAction_LargerBallotAcceptors(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b':Ballot, v':Value) 
    requires c.WF() && ds.WF(c)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)

    requires Chosen(c, ds', b', v')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires LargerBallotAcceptMsgs(c, ds', b', v')
    ensures LargerBallotAcceptors(c, ds', b', v')
{}


lemma AgreementChosenInv_SomeChosen_AccAction_LargerBallotPromiseMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b':Ballot, v':Value) 
    requires c.WF() && ds.WF(c)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)

    requires Chosen(c, ds', b', v')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires LargerBallotAcceptMsgs(c, ds', b', v')
    ensures LargerBallotPromiseMsgs(c, ds', b', v')
{}


lemma AgreementChosenInv_SomeChosen_AccAction_LargerBallotProposeMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b':Ballot, v':Value) 
    requires c.WF() && ds.WF(c)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)

    requires Chosen(c, ds', b', v')
    requires ProposeMsgImpliesQuorumOfPromise(c, ds')
    requires AcceptMsgImpliesProposeMsg(c, ds')
    requires OneValuePerBallot_ProposeMsg(c, ds')
    requires LargerBallotsPromiseQrms(c, ds', b')
    requires LargerBallotPromiseMsgs(c, ds', b', v')
    ensures LargerBallotProposeMsgs(c, ds', b', v')
{
    forall p | isProposePkt(ds', p) && BalLtEq(b', p.msg.bal)
    ensures p.msg.val == v'
    {
        var b, v := p.msg.bal, p.msg.val;
        if b == b' {
            assert v' == v;     // by OneValuePerBallot_ProposeMsg
        } else {
            var prom_qrm :| && QuorumOfPromiseMsgs(c, ds', prom_qrm, b)
                            && (|| PromisePktWithHighestBallot(prom_qrm).msg.vb.v == v
                                || PromisePktWithHighestBallot(prom_qrm).msg.vb.v == Nil);
            var prom := PromisePktWithHighestBallot(prom_qrm);
            var prom_smaller:Packet :| prom_smaller in prom_qrm && BalLtEq(b', prom_smaller.msg.vb.b);  // because Quorum must have seen b (LargerBallotsPromiseQrms)
            lemma_BalLtEqTransitivity(b', prom_smaller.msg.vb.b, prom.msg.vb.b);
            assert PromisePktWithHighestBallot(prom_qrm).msg.vb.v == v';     // because LargerBallotPromiseMsgs
        }
    }
}

lemma AgreementChosenInv_SomeChosen_AccAction_LargerBallotPhase2LeadersV(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b':Ballot, v':Value) 
    requires c.WF() && ds.WF(c)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires recvIos[0].msg.Propose?
    requires AcceptorAccept(ds.acceptors[actor.idx], ds'.acceptors[actor.idx], recvIos[0], sendIos);   

    requires Chosen(c, ds', b', v')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires LargerBallotsPromiseQrms(c, ds', b')
    requires LargerBallotPromiseMsgs(c, ds', b', v')
    ensures LargerBallotPhase2LeadersV(c, ds', b', v')
{
    AgreementChosenInv_NoneChosen_AccAction_NewChosenV_P2LeaderV(c, ds, ds', actor, recvIos, sendIos, b', v');
}





lemma AgreementChosenInv_SomeChosen_OldValueChosen(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidAccId(actor)
    requires Chosen(c, ds, b, v) 
    ensures forall b', v' | Chosen(c, ds', b', v') :: v' == v
{
    forall b', v' | Chosen(c, ds', b', v') 
    ensures v' == v
    {
        if BalLtEq(b, b') {
            if Chosen(c, ds, b', v') {
                assert v' == v;
            } else {
                /* This must be an accept step that lead to (b', v') being chosen. There
                * is at least one Accept(b', v') in ds. This msg has v' == v by LargerBallotAcceptMsgs
                */
                
                var qrm' :| QuorumOfAcceptMsgs(c, ds', qrm', b') && AccPacketsHaveValueV(qrm', v');
                lemma_NewChosenImpliesAcceptStep(c, ds, ds', actor, recvIos, sendIos, b', v');
                var new_pkt := sendIos[0];
                assert new_pkt.msg.val == v';
                
                // Prove new_pkt must be in qrm'
                if new_pkt !in qrm' {
                    lemma_NewPacketsComeFromSendIos(c, ds, ds', actor, recvIos, sendIos);
                    forall p | p in qrm' 
                    ensures p in ds.network.sentPackets
                    {
                        lemma_SingleElemList3(sendIos, new_pkt, p);
                    }
                    assert Chosen(c, ds, b', v');
                    assert false;
                }

                assert |qrm'| >= 2;
                lemma_Set_MultiElem(qrm', new_pkt);
                var old_accpt :| old_accpt in qrm' && old_accpt != new_pkt;
                assert old_accpt.msg.val == v';
                assert old_accpt in ds.network.sentPackets;
                assert isAcceptPkt(ds, old_accpt) && BalLtEq(b, old_accpt.msg.bal);
                assert old_accpt.msg.val == v;
                assert v' == v;
            }
        } else {
            assert BalLt(b', b);
            if Chosen(c, ds, b', v') {
                assert v' == v;
            } else {

            }
            // TODO
            assume false;
        }
    }
}


















lemma AgreementChosenInv_SomeChosen_LdrAction(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_Common(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    ensures Agreement_Chosen_Inv_ChosenProperties(c, ds')
{
    forall b, v | Chosen(c, ds', b, v) 
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v)
    {
        lemma_NoNewAcceptsImpliesNoNewChosen(c, ds, ds');
        AgreementChosenInv_SomeChosen_LdrAction_LargerBallotPhase2LeadersV(c, ds, ds', actor, recvIos, sendIos, b, v);
        AgreementChosenInv_SomeChosen_LdrAction_LargerBallotAcceptors(c, ds, ds', actor, recvIos, sendIos, b, v);
        AgreementChosenInv_SomeChosen_LdrAction_LargerBallotAcceptMsgs(c, ds, ds', actor, recvIos, sendIos, b, v);       
        AgreementChosenInv_SomeChosen_LdrAction_LargerBallotPromiseMsgs(c, ds, ds', actor, recvIos, sendIos, b, v);   
        AgreementChosenInv_SomeChosen_LdrAction_LargerBallotProposeMsgs(c, ds, ds', actor, recvIos, sendIos, b, v); 
        AgreementChosenInv_SomeChosen_LdrAction_LargerBallotsPromiseQrms(c, ds, ds', actor, recvIos, sendIos, b, v); 
    }
}



lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotPhase2LeadersV(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires Agreement_Chosen_Inv(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds, b, v)
    requires Chosen(c, ds', b, v) 
    ensures LargerBallotPhase2LeadersV(c, ds', b, v)
{
    forall idx | 
        && c.ValidLdrIdx(idx) 
        && BalLtEq(b, ds'.leaders[idx].ballot) 
        && LeaderInPhase2(c, ds', idx) 
    ensures LeaderHasValueV(c, ds', idx, v)
    {
        if idx == actor.idx {
            var l, l' := ds.leaders[idx], ds'.leaders[idx];
            match l.state {
                case P1a => 
                    lemma_LdrP1aGoToP1(c, ds, ds', actor, recvIos, sendIos);
                    assert false;
                case P1b => 
                    AgreementChosenInv_SomeChosen_LdrAction_LargerBallotPhase2LeadersV_helper(c, ds, ds', actor, recvIos, sendIos, b, v);
                case P2a => 
                    assert l'.val == l.val;
                    assert LeaderHasValueV(c, ds', idx, v);
                case P2b => {
                    match recvIos[0].msg {
                        case Accept(bal, val) => 
                            lemma_LdrProcessAcceptDoesNotChangeValueAndBallot(c, ds, ds', actor, recvIos, sendIos);
                            assert LeaderHasValueV(c, ds', idx, v);
                        case Preempt(bal) => 
                            if BalLt(l.ballot, recvIos[0].msg.bal) {
                                assert l'.state == P1a;
                                assert false;
                            } else {
                                assert l'.val == l.val;
                                assert LeaderHasValueV(c, ds', idx, v);
                            }
                        case _ => 
                            assert l'.val == l.val;
                            assert LeaderHasValueV(c, ds', idx, v);
                    }
                }
                case Decided => 
                    assert l'.state == Decided;
                    assert false;
            }
        } else {
            assert ds'.leaders[idx] == ds.leaders[idx];
            assert LeaderInPhase2(c, ds, idx);
            assert LeaderHasValueV(c, ds', idx, v);
        }
    }
}

lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotPhase2LeadersV_helper(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires c.WF() && ds.WF(c)
    requires Trivialities(c, ds)
    
    // a la carte for faster verificaion
    requires LdrPromisesSetCorrespondToPromiseMsg(c, ds)
    requires LdrPromisesSetHaveUniqueSrc(c, ds)
    requires LdrPromisesSetHaveLeaderBallot(c, ds)
    requires LargerBallotsPromiseQrms(c, ds, b)
    requires LargerBallotPromiseMsgs(c, ds, b, v)
    requires SameBallotLeaderNotInPhase1(c, ds, b)

    requires ds'.WF(c) && Trivialities(c, ds')
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds', b, v) 

    requires Chosen(c, ds, b, v);
    requires BalLtEq(b, ds'.leaders[actor.idx].ballot) 
    requires LeaderInPhase2(c, ds', actor.idx) 
    requires ds.leaders[actor.idx].state == P1b
    ensures LeaderHasValueV(c, ds', actor.idx, v)
{
    var l, l' := ds.leaders[actor.idx], ds'.leaders[actor.idx];
    var pkt := recvIos[0];
    match pkt.msg {
        case Promise(bal, valbal) => 
            assert l.ballot == l'.ballot;
            if pkt.msg.bal == l.ballot && !exists p :: p in l.promises && p.src == pkt.src {
                if |l.promises| == 2*l.consts.f {
                    assert l'.state == P2a;
                    var promises := l.promises + {pkt};
                    assert BalLtEq(b, l'.ballot);
                    assert PromisesSetCorrespondToPromiseMsg(c, ds, actor.idx);
                    assert isPromisePkt(ds, pkt);
                    lemma_Set_Union_Property(l.promises, promises, pkt);
                    forall p | p in promises 
                    ensures isPromisePkt(ds, p) {
                        if p == pkt {
                            assert isPromisePkt(ds, p);
                        } else {
                            assert p in l.promises;
                            assert isPromisePkt(ds, p);
                        }
                    }
                    assert QuorumOfPromiseMsgs(c, ds, promises, l.ballot);
                    if BalLt(b, l.ballot) {
                        assert QuorumHasSeenB(c, promises, b);
                        lemma_QrmSeenBAndAllLargerBalsHaveSameV(c, ds, promises, l.ballot, b, v);
                    } else {
                        assert false;
                    }               
                } else {
                    assert l'.state == l.state;
                    assert false;
                }
            } else {
                assert l'.state == l.state;
                assert false;
            }
        case Preempt(bal) => 
            if BalLt(l.ballot, pkt.msg.bal) {
                assert l'.state == P1a;
                assert false;
            } else {
                assert l'.state == l.state;
                assert false;
            }
        case _ => 
            assert l'.state == l.state;
            assert false;
    }
}


lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotAcceptors(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires c.WF() && ds.WF(c)
    requires Trivialities(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_ChosenProperties(c, ds)
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds, b, v) 
    requires Chosen(c, ds', b, v) 
    ensures LargerBallotAcceptors(c, ds', b, v)
{
    forall i | c.ValidAccIdx(i) 
    ensures ds'.acceptors[i] == ds.acceptors[i] {}
}


lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotAcceptMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires c.WF() && ds.WF(c)
    requires Trivialities(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_ChosenProperties(c, ds)
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds, b, v) 
    requires Chosen(c, ds', b, v) 
    ensures LargerBallotAcceptMsgs(c, ds', b, v)
{}


lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotPromiseMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires c.WF() && ds.WF(c)
    requires Trivialities(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_ChosenProperties(c, ds)
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds, b, v) 
    requires Chosen(c, ds', b, v) 
    ensures LargerBallotPromiseMsgs(c, ds', b, v)
{}


lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotProposeMsgs(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires c.WF() && ds.WF(c)
    requires Trivialities(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_ChosenProperties(c, ds)
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds, b, v) 
    requires Chosen(c, ds', b, v) 
    ensures LargerBallotProposeMsgs(c, ds', b, v)
{}


lemma AgreementChosenInv_SomeChosen_LdrAction_LargerBallotsPromiseQrms(
c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>, b:Ballot, v:Value)
    requires c.WF() && ds.WF(c)
    requires Trivialities(c, ds)
    requires ds'.WF(c) && Trivialities(c, ds')
    requires Agreement_Chosen_Inv_ChosenProperties(c, ds)
    requires Next(c, ds, ds')
    requires PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos)
    requires c.ValidLdrId(actor)
    requires SomeValueChosen(c, ds)
    requires Chosen(c, ds, b, v) 
    requires Chosen(c, ds', b, v) 
    ensures LargerBallotsPromiseQrms(c, ds', b)
{
    forall b' | BalLt(b, b') 
    ensures LargerBalQuorumHasSeenB(c, ds', b, b')
    {
        forall qrm:set<Packet> | QuorumOfPromiseMsgs(c, ds', qrm, b') 
        ensures QuorumHasSeenB(c, qrm, b)
        {
            assert forall p | p in qrm :: p in ds.network.sentPackets;
            assert QuorumOfPromiseMsgs(c, ds, qrm, b');
            assert QuorumHasSeenB(c, qrm, b);
        }
    }
}


}