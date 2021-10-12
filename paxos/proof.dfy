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
        case Promise(bal, val, valbal) => val != v ==> val == Nil
        case Propose(bal, val) => val == v
        case Accept(bal) =>  true
        case Preempt(bal, val) => val != v ==> val == Nil
    }
}

predicate Validity_Inv_AllAccAcceptsV(c:Constants, ds:DistrSys, v:Value) 
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> forall i | c.ValidAccIdx(i) :: ds.acceptors[i].accepted != v ==> ds.acceptors[i].accepted == Nil 
}

predicate Validity_Inv_AllLdrProposeV(c:Constants, ds:DistrSys, v:Value)
    requires c.WF()
    requires ds.WF(c)
{
    AllProcessesInitV(c, ds, v) ==> 
    && (forall i | c.ValidLdrIdx(i) :: ds.leaders[i].val == v)
    && (forall i | c.ValidLdrIdx(i) :: 
            forall p | p in ds.leaders[i].promises 
            :: p.val != Nil ==> p.val == v)
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
    && FutureBallotsDecisionsProperty(c, ds)
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
                    lemma_FutureBallotsDecisionsProperty(c, ds, ds');
                    assert LeaderIdxDecidedV(c, ds', i, v, b); 
                    assert false;
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

/* Assumption that if v is decided with ballot b, then all values decided with ballots
* b' >= b must be of v */
predicate FutureBallotsDecisionsProperty(c:Constants, ds:DistrSys)
    requires c.WF() && ds.WF(c)
{
    forall v, b, i | c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b) 
    :: 
    (forall v', b', i' | 
        && c.ValidLdrIdx(i') 
        && BalLtEq(b, b') 
        && LeaderIdxDecidedV(c, ds, i', v', b') 
        :: v' == v)
}


lemma lemma_FutureBallotsDecisionsProperty(c:Constants, ds:DistrSys, ds':DistrSys)
    requires c.WF() && ds.WF(c)
    requires FutureBallotsDecisionsProperty(c, ds)
    requires Next(c, ds, ds')
    ensures FutureBallotsDecisionsProperty(c, ds');
{
    assume false;
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