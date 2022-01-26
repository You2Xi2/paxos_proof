include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_helper.dfy"
include "proof_axioms.dfy"
include "proof_agreement_invariants.dfy"

module Proof_Agreement_ChosenProperties_2 {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Helper
import opened Proof_Axioms
import opened Proof_Agreement_Invs



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
        assume false;
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
    assume false;
    lemma_NoNewAcceptsImpliesNoNewChosen(c, ds, ds');
    forall b, v | Chosen(c, ds', b, v) 
    ensures Agreement_Chosen_Inv_SomeValChosen(c, ds', b, v)
    {
        assert LargerBallotPhase2LeadersV(c, ds', b, v);
        assert LargerBallotAcceptors(c, ds', b, v);
        assert LargerBallotAcceptMsgs(c, ds', b, v);
        assert LargerBallotPromiseMsgs(c, ds', b, v);
        assert LargerBallotProposeMsgs(c, ds', b, v);
        assert LargerBallotsPromiseQrms(c, ds', b);
    }
}

}