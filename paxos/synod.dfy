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
        && |ldr_vals| == |ldr_ids|
        && |acc_ids| == 2*f+1
        && ValidTypes()
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

    predicate UniqueIds() {
        && (forall i, j | ValidLdrIdx(i) && ValidLdrIdx(j) && ldr_ids[i]==ldr_ids[j] :: i == j)
        && (forall i, j | ValidAccIdx(i) && ValidAccIdx(j) && acc_ids[i]==acc_ids[j] :: i == j)
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
    && exists src, recvIos, sendIos :: PaxosNextOneAgent(s, s', src, recvIos, sendIos)
}


predicate PaxosNextOneAgent(s:DistrSys, s':DistrSys, src:Id, recvIos:seq<Packet>, sendIos:seq<Packet>) 
{
    && ValidSrc(s, src)
    && PaxosNextOneAgent_Agent(s, s', src, recvIos, sendIos)
    && s.network.nextStep == IoStep(src, recvIos, sendIos)
    && EnvironmentNext(s.network, s'.network)
}

predicate PaxosNextOneAgent_Agent(s:DistrSys, s':DistrSys, src:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)
    requires ValidSrc(s, src)
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

predicate ValidSrc(s:DistrSys, src:Id) {
     match src.agt {
        case Ldr() => 0 <= src.idx < |s.leaders|
        case Acc() => 0 <= src.idx < |s.acceptors|
    }
}
}