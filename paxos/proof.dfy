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
predicate Agreement_Inv(c:Constants, ds:DistrSys, b:Ballot) 
{
    && c.WF()
    && ds.WF(c)
    && Agreement(c, ds)
}


/* Init ==> Agreement_Inv */
lemma InitImpliesAgreementInv(c:Constants, ds:DistrSys, b:Ballot) 
    requires Init(c, ds)
    ensures Agreement_Inv(c, ds, b)
{}


/* Agreement_Inv && Next ==> Agreement_Inv' */
lemma NextPreservesAgreementInv(c:Constants, b:Ballot, ds:DistrSys, ds':DistrSys) 
    requires Agreement_Inv(c, ds, b)
    requires Next(c, ds, ds')
    ensures Agreement_Inv(c, ds', b)
{
    if exists v, b, i :: c.ValidLdrIdx(i) && LeaderIdxDecidedV(c, ds, i, v, b) {
        // If someone has decided in ds
        // TODO
        assume false;
        assert Agreement(c, ds');
    } else {
        // If no one has decided in ds
        var src, recvIos, sendIos :| PaxosNextOneAgent(c, ds, ds', src, recvIos, sendIos);
        if src.agt == Acc {
            assert forall l | l in ds'.leaders :: !l.state.Decided?;
            assert forall l | l in ds'.leaders :: !l.state.Decided?;
            assert forall v, b, i | c.ValidLdrIdx(i) :: !LeaderIdxDecidedV(c, ds', i, v, b);
            assert Agreement(c, ds');
        } else {
            // TODO
            assume false;
            assert Agreement(c, ds');
        }
    }
}






/* Assumption that if v is decided with ballot b, then all values decided with ballots
* b' >= b must be of v */
predicate FutureProposalsInv(c:Constants, ds:DistrSys, i:int, v:Value, b:Ballot)
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i) 
{
    LeaderIdxDecidedV(c, ds, i, v, b) 
    ==> 
    (forall v', b', i' | 
        && c.ValidLdrIdx(i') 
        && BalLtEq(b, b') 
        && LeaderIdxDecidedV(c, ds, i', v', b') 
        :: v' == v)
}


lemma lemma_FutureProposalsInv(c:Constants, v:Value, i:int, b:Ballot, ds:DistrSys, ds':DistrSys)
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(i) 
    requires FutureProposalsInv(c, ds, i, v, b)
    requires Next(c, ds, ds')
    ensures FutureProposalsInv(c, ds', i, v, b);
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