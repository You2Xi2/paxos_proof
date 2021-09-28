include "network.dfy"
include "agents.dfy"

module Synod {
import opened Network
import opened Agents


datatype DistrSys = DistrSys(
    network: Environment<Id, Message>,
    leaders: seq<Leader<Id, Ballot, Value>>,
    acceptors: seq<Acceptor<Ballot, Value>>
)

datatype Step = PaxosStep(src:Id)



}