include "types.dfy"
include "network.dfy"
include "agents.dfy"

module Synod {
import opened Network
import opened Agents
import opened Types


datatype DistrSys = DistrSys(
    network: Environment,
    leaders: seq<Leader>,
    acceptors: seq<Acceptor>
)


/*****************************************************************************************
*                                        DS Init                                         *
*****************************************************************************************/
predicate Init(s:DistrSys, f:nat, l:nat, accConf:seq<Id>) 
    requires f >= 1;
    requires l >= 1;
    requires ValidAccConf(f, accConf)
{
    && EnvironmentInit(s.network)
    && |s.leaders| == l
    && (forall i | 0 <= i < l :: LeaderInit(s.leaders[i], Id(Ldr, i), accConf, f, V(i)))
    && |s.acceptors| == 2*f+1
    && (forall i | 0 <= i < 2*f+1 :: AcceptorInit(s.acceptors[i], accConf[i]))
}

predicate ValidAccConf(f:nat, accConf:seq<Id>) {
    && |accConf| == 2*f+1
    && (forall i | 0 <= i < |accConf| :: accConf[i] == Id(Acc, i))
}

// predicate AccConfUnique(accConf:seq<Id>) {
//     forall i,j | 0 <= i < |accConf| && 0 <= j < |accConf| 
//     :: accConf[i].idx == accConf[j].idx ==> i == j
// }


/*****************************************************************************************
*                                        DS Next                                         *
*****************************************************************************************/

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