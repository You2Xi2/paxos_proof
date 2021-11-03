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
    forall v, b, idx | c.ValidLdrIdx(idx) && LeaderIdxDecidedV(c, ds, idx, v, b) 
    :: AllDecidedProcessesDecidesV(c, ds, v)
}

predicate LeaderIdxDecidedV(c:Constants, ds:DistrSys, idx:int, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    && b != Bottom
    && ds.leaders[idx].state == Decided 
    && ds.leaders[idx].val == v
    && ds.leaders[idx].ballot == b
}


/* Invariants for establishing Agreement */
predicate Agreement_Inv(c:Constants, ds:DistrSys) 
{
    && c.WF()
    && ds.WF(c)
    && Agreement(c, ds)
    && LdrBallotNotBottom(c, ds)
    && Agreement_Inv_Lemma(c, ds)
}


predicate LdrBallotNotBottom(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    && (forall l | l in ds.leaders :: l.ballot != Bottom)
    // && (forall m | m in ds.network.sentPackets ::
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

    if exists v, b, i :: c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b) {
        // If someone has decided in ds
        NextPreservesAgreementInv_Case_ExistingDecision(c, ds, ds');
    } else {
        // If no one has decided in ds
        NextPreservesAgreementInv_Case_NoExistingDecision(c, ds, ds');
    }
}

lemma NextPreservesAgreementInv_Case_ExistingDecision(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires exists v, b, i :: c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b)
    ensures Agreement_Inv(c, ds')
{
    NextPreservesAgreementInvLemma(c, ds, ds');
    var v, b, i :| c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b);
    var actor, recvIos:seq<Packet>, sendIos:seq<Packet> :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt.Ldr? {
        var l, l' := ds.leaders[actor.idx], ds'.leaders[actor.idx];
        if l.state == P2b && recvIos[0].msg.Accept? {
            var src, msg := recvIos[0].src, recvIos[0].msg;
            if msg.bal == l.ballot && src !in l.accepts && |l.accepts| == 2*l.consts.f {
                var b', v' := l.ballot, l.val;
                if v' != v {
                    assert LeaderIdxDecidedV(c, ds', actor.idx, v', b'); 
                    assert LeaderIdxDecidedV(c, ds', i, v, b); 
                    if BalLtEq(b, b'){
                        assert false;
                    } else {
                        assert BalLtEq(b', b);
                        assert false;
                    }
                }
            }
        } 
    }
}

lemma NextPreservesAgreementInv_Case_NoExistingDecision(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds)
    requires Next(c, ds, ds')
    requires forall v, b, i | c.ValidLdrIdx(i) :: !LeaderIdxDecidedV(c, ds, i, v, b)
    ensures Agreement_Inv(c, ds')
{
    NextPreservesAgreementInvLemma(c, ds, ds');
    var src, recvIos, sendIos :| PaxosNextOneAgent(c, ds, ds', src, recvIos, sendIos);
    forall l | l in ds.leaders 
    ensures !l.state.Decided? {
        if l.state.Decided? {
            var v, b, i := l.val, l.ballot, l.consts.id.idx;
            assert b != Bottom;
            assert LeaderIdxDecidedV(c, ds, i, v, b);
            assert false;
        }
    }
}


///////////////////////          Agreement Sub-Lemma         /////////////////////////////


predicate Agreement_Inv_Lemma(c:Constants, ds:DistrSys) 
{
    && c.WF()
    && ds.WF(c)
    && LeaderPromisesSetProperty(c, ds)
    && Agreement_Safey(c, ds)
    && (forall v, b, i | c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b) 
        :: AgreementInvProperties_Decided(c, ds, v, b))
}

predicate Agreement_Safey(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall v, b, i | c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b)
    :: LargerBallotsDecideV(c, ds, v, b)
}

predicate AgreementInvProperties_Decided(c:Constants, ds:DistrSys, v:Value, b:Ballot)
    requires c.WF() && ds.WF(c)
{
    && v != Nil
    // && LargerBallotsPromiseQrms(c, ds, v, b)
    && LargerBallotPhase2LeadersV(c, ds, v, b)
    && LargerBallotAcceptors(c, ds, v, b)
    && LargerBallotPromiseMsgs(c, ds, v, b)
    && LargerBallotProposalMsgs(c, ds, v, b)
}


predicate LeaderPromisesSetProperty(c:Constants, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
{
    forall i | c.ValidLdrIdx(i) :: (
        forall p | p in ds.leaders[i].promises :: 
            && p in ds.network.sentPackets
            && p.msg.Promise?
            && p.msg.bal == ds.leaders[i].ballot
    )
}


/* If v is decided with ballot b, then all values decided with ballots
* b' >= b must be of v */
predicate LargerBallotsDecideV(c:Constants, ds:DistrSys, v:Value, b:Ballot)
    requires c.WF() && ds.WF(c)
{
    forall b', i' | 
        && c.ValidLdrIdx(i') && BalLtEq(b, b') 
        && LeaderHasDecided(c, i', ds) && LeaderHasBallotB(c, i', ds, b') 
    :: LeaderHasValueV(c, i', ds, v)
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

/* If v is decided with ballot b, then all phase 2 leaders with ballots
* b' >= b must be of v */
predicate LargerBallotPhase2LeadersV(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall b', i' | 
        && c.ValidLdrIdx(i') && BalLtEq(b, b') 
        && LeaderInPhase2(c, i', ds) && LeaderHasBallotB(c, i', ds, b')
    :: LeaderHasValueV(c, i', ds, v)
}

/* If v is decided with ballot b, then there is a quorum q of acceptors such that all in q
* accepted b' >= b with value v */
predicate QuorumOfAcceptorsAcceptedBV(c:Constants, ds:DistrSys, q:set<int>, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
    requires QuorumOfAcceptors(c, q)
{
    forall idx | idx in q ::
        && ds.acceptors[idx].accepted.v == v
        && BalLtEq(b, ds.acceptors[idx].accepted.b)
}

/* If v is decided with ballot b, then for any acceptor that accepted a ballot b'>=b, 
* the accepted value is v */
predicate LargerBallotAcceptors(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall idx | c.ValidAccIdx(idx) && BalLtEq(b, ds.acceptors[idx].accepted.b)
    :: ds.acceptors[idx].accepted.v == v
}

/* If v is decided with ballot b, then for any Promise msgs with valbal ballot b'>=b, 
* the valbal value is v */
predicate LargerBallotPromiseMsgs(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets && p.msg.Promise? && BalLtEq(b, p.msg.vb.b)
    :: p.msg.vb.v == v
}

/* If v is decided with ballot b, then for any Proposal msgs with ballot b'>=b, 
* the value is v */
predicate LargerBallotProposalMsgs(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
    requires c.WF() && ds.WF(c)
{
    forall p | p in ds.network.sentPackets && p.msg.Propose? && BalLtEq(b, p.msg.bal)
    :: p.msg.val == v
}


/* Main theorem for Agreement_Inv_Lemma */
lemma NextPreservesAgreementInvLemma(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv_Lemma(c, ds)
    requires Next(c, ds, ds')
    ensures Agreement_Inv_Lemma(c, ds')
{
    if exists v, b, i :: c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b) {
        var v, b, i :| c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b);
        NextPreservesAgreementInvLemma_1(c, ds, ds', i, v, b);
    } else {
        assume false;
    }
}


lemma NextPreservesAgreementInvLemma_1(c:Constants, ds:DistrSys, ds':DistrSys, i:int, v:Value, b:Ballot) 
    requires Agreement_Inv_Lemma(c, ds)
    requires Next(c, ds, ds')
    requires c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b);
    ensures Agreement_Inv_Lemma(c, ds')
{
    // assert v != Nil;
    // Lemma_LargerBallotAcceptors_1(c, ds, ds', i, v, b);
    // Lemma_LargerBallotsDecideV_1(c, ds, ds', i, v, b);
    // assume LargerBallotsPromiseQrms(c, ds', v, b);  // TODO: Assume this for now
    // Lemma_LargerBallotPhase2LeadersV_1(c, ds, ds', i, v, b);
    // assert AgreementInvProperties_Decided(c, ds', v, b);
    
    forall v', b', i' | c.ValidLdrIdx(i') && LeaderIdxDecidedV(c, ds', i', v', b')
    ensures && LargerBallotsDecideV(c, ds', v', b')
            && AgreementInvProperties_Decided(c, ds', v', b');
    {
        if BalLtEq(b, b') {
            assume v' == v;
            assert v' != Nil;

            assert LargerBallotsDecideV(c, ds', v', b');


            // assert LargerBallotsPromiseQrms(c, ds', v', b');
            assert LargerBallotPhase2LeadersV(c, ds', v', b');
            assert LargerBallotAcceptors(c, ds', v', b');
            assert LargerBallotPromiseMsgs(c, ds', v', b');
            assert LargerBallotProposalMsgs(c, ds', v', b');
            assert AgreementInvProperties_Decided(c, ds', v', b');
        } else {
            assume false;
        }
    }
    assert Agreement_Inv_Lemma(c, ds');
}




lemma Lemma_LargerBallotAcceptors_1(c:Constants, ds:DistrSys, ds':DistrSys,i:int, v:Value, b:Ballot) 
    requires Agreement_Inv_Lemma(c, ds)
    requires Next(c, ds, ds')
    requires c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b)
    ensures LargerBallotAcceptors(c, ds', v, b)
{}

lemma Lemma_LargerBallotsDecideV_1(c:Constants, ds:DistrSys, ds':DistrSys,i:int, v:Value, b:Ballot) 
    requires Agreement_Inv_Lemma(c, ds)
    requires Next(c, ds, ds')
    requires c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b)
    ensures LargerBallotsDecideV(c, ds', v, b)
{}

lemma Lemma_LargerBallotPhase2LeadersV_1(c:Constants, ds:DistrSys, ds':DistrSys,i:int, v:Value, b:Ballot) 
    requires Agreement_Inv_Lemma(c, ds)
    requires Next(c, ds, ds')
    requires c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b)
    ensures LargerBallotPhase2LeadersV(c, ds', v, b)
{
    var actor, recvIos:seq<Packet>, sendIos :| PaxosNextOneAgent(c, ds, ds', actor, recvIos, sendIos);
    if actor.agt == Ldr {
        var l, l' := ds.leaders[actor.idx], ds'.leaders[actor.idx];
        if l.state == P1b && BalLtEq(b, l.ballot) {
            var pkt := recvIos[0];
            if pkt.msg.Promise? {
                var src, msg := pkt.src, pkt.msg;
                if  && msg.bal == l.ballot 
                    && (!exists p :: p in l.promises && p.src == src) 
                    && |l.promises| == 2*l.consts.f 
                {
                    var qrm := l.promises + {pkt};
                    assert QuorumOfPromiseMsgs(c, ds, qrm, l.ballot);
                    assert PromiseWithHighestBallot(qrm).v == v;
                    assert LargerBallotPhase2LeadersV(c, ds', v, b);
                }
            }
        }
    }
}





// predicate Agreement_Inv_AcceptedByQuorum(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
//     requires c.WF() && ds.WF(c)
// {
//     SomeProcessDecidedV(c, ds, v, b) ==> (
//         exists quorum ::
//             && QuorumOfAcceptors(c, quorum)
//             && AcceptedByQuroum(c, ds, quorum, v, b)
//     )
// }

// predicate AcceptedByQuroum(c:Constants, ds:DistrSys, q:set<int>, v:Value, b:Ballot) 
//     requires c.WF() && ds.WF(c)
//     requires QuorumOfAcceptors(c, q)
// {
//     forall idx | idx in q ::
//         && ds.acceptors[idx].accepted == v
//         && BalLtEq(b, ds.acceptors[idx].promised)
// }


// predicate Agreement_Inv_Messages(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
//     requires c.WF() && ds.WF(c)
// {
//     SomeProcessDecidedV(c, ds, v, b) 
//     ==> 
//     (forall pkt | pkt in ds.network.sentPackets && BalLtEq(b, pkt.msg.bal)
//     :: ProposeAndPreemptContainsV(pkt.msg, v))
// }

// predicate ProposeAndPreemptContainsV(m:Message , v:Value) {
//     match m {
//         case Propose(bal, val) => val == v
//         case Preempt(bal, val) => val == v
//         case _ => true
//     }
// }

// predicate Agreement_Inv_P2Leaders(c:Constants, ds:DistrSys, v:Value, b:Ballot) 
//     requires c.WF() && ds.WF(c)
// {
//     SomeProcessDecidedV(c, ds, v, b) 
//     ==> 
//     (forall i | 
//         && c.ValidLdrIdx(i) 
//         && LeaderInPhase2(c, i, ds) 
//         && BalLtEq(b, ds.leaders[i].ballot)
//     :: ds.leaders[i].val == v)
// }

}