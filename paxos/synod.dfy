include "types.dfy"
include "network.dfy"
include "agents.dfy"

module Synod {
import opened Network
import opened Agents
import opened Types


datatype Constants = Constants(f:nat, ldr_ids:seq<Id>, ldr_vals:seq<Value>, acc_ids:seq<Id>) {
    predicate WF() {
        && f >= 1
        && |ldr_ids| >= 1
        && |acc_ids| == 2*f+1
        && ValidLdrVals()
        && ValidTypes()
        && ValidIds()
        && UniqueIds()
    }

    predicate ValidLdrIdx(i:int) {
        0<=i<|ldr_ids|
    }

    predicate ValidAccIdx(i:int) {
        0<=i<|acc_ids|
    }

    predicate ValidTypes() {
        && (forall l | l in ldr_ids :: l.agt.Ldr?)
        && (forall l | l in acc_ids :: l.agt.Acc?)
    }

    predicate ValidLdrVals() {
        && |ldr_vals| == |ldr_ids|
        && forall i | ValidLdrIdx(i) :: ldr_vals[i] != Nil
    }

    predicate UniqueIds() {
        && (forall i, j | ValidLdrIdx(i) && ValidLdrIdx(j) && ldr_ids[i]==ldr_ids[j] :: i == j)
        && (forall i, j | ValidAccIdx(i) && ValidAccIdx(j) && acc_ids[i]==acc_ids[j] :: i == j)
    }

    predicate ValidIds() {
        && (forall i | ValidLdrIdx(i) :: ldr_ids[i].idx == i)
        && (forall i | ValidAccIdx(i) :: acc_ids[i].idx == i)
    }
}

datatype DistrSys = DistrSys(
    network: Environment,
    leaders: seq<Leader>,
    acceptors: seq<Acceptor>
) {
    predicate WF(c: Constants)
        requires c.WF()
    {
        && |leaders| == |c.ldr_ids|
        && |acceptors| == |c.acc_ids|
        && (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.id == c.ldr_ids[i])
        && (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.initval == c.ldr_vals[i])
        && (forall i | c.ValidAccIdx(i) :: acceptors[i].consts.id == c.acc_ids[i])
    }
}


/*****************************************************************************************
*                                        DS Init                                         *
*****************************************************************************************/
predicate Init(c:Constants, s:DistrSys) 
{
    && c.WF()
    && s.WF(c)
    && EnvironmentInit(s.network)
    && |s.leaders| == |c.ldr_ids|
    && |s.acceptors| == |c.acc_ids|
    && (forall i | c.ValidLdrIdx(i) :: LeaderInit(s.leaders[i], c.ldr_ids[i], c.acc_ids, c.f, c.ldr_vals[i]))
    && (forall i | c.ValidAccIdx(i) :: AcceptorInit(s.acceptors[i], c.acc_ids[i]))
}


/*****************************************************************************************
*                                        DS Next                                         *
*****************************************************************************************/

predicate Next(c:Constants, s:DistrSys, s':DistrSys) {
    && c.WF()
    && s.WF(c)
    && s'.WF(c)
    && exists actor, recvIos, sendIos :: PaxosNextOneAgent(c, s, s', actor, recvIos, sendIos)
}


predicate PaxosNextOneAgent(c:Constants, s:DistrSys, s':DistrSys, actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires c.WF() && s.WF(c) && s'.WF(c)
{
    && ValidActor(c, actor)
    && PaxosNextOneAgent_Agent(c, s, s', actor, recvIos, sendIos)
    && s.network.nextStep == IoStep(actor, recvIos, sendIos)
    && EnvironmentNext(s.network, s'.network)
}

predicate PaxosNextOneAgent_Agent(c:Constants, s:DistrSys, s':DistrSys, src:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires c.WF() && s.WF(c) && s'.WF(c)
    requires ValidActor(c, src)
{
    match src.agt {
        case Ldr() => 
            && s'.acceptors == s.acceptors
            && |s'.leaders| == |s.leaders|
            && s'.leaders == s.leaders[src.idx := s'.leaders[src.idx]]
            && LeaderNext(s.leaders[src.idx], s'.leaders[src.idx], recvIos, sendIos)
        case Acc() => 
            && s'.leaders == s.leaders
            && |s'.acceptors| == |s.acceptors|
            && s'.acceptors == s.acceptors[src.idx := s'.acceptors[src.idx]]
            && AcceptorNext(s.acceptors[src.idx], s'.acceptors[src.idx], recvIos, sendIos)
    }
}

predicate ValidActor(c:Constants, actor:Id) 
    requires c.WF()
{
     match actor.agt {
        case Ldr => c.ValidLdrIdx(actor.idx)
        case Acc => c.ValidAccIdx(actor.idx)
    }
}


/*****************************************************************************************
*                                        Utils                                           *
*****************************************************************************************/

predicate QuorumOfAcceptors(c:Constants, q:set<int>) 
    requires c.WF()
{
    && |q| >= c.f + 1
    && forall idx | idx in q :: c.ValidAccIdx(idx)
}

predicate LeaderInPhase2(c:Constants, idx:int, ds:DistrSys) 
    requires c.WF() && ds.WF(c)
    requires c.ValidLdrIdx(idx)
{
    ds.leaders[idx].state == P2a || ds.leaders[idx].state == P2b
}

}