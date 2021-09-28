include "types.dfy"

module Agents {
import opened Types


/*****************************************************************************************
*                                Acceptor State Machine                                  *
*****************************************************************************************/

datatype Acceptor = Acceptor(id:Id, promised:Ballot, accepted:Value)

/* Acceptor initial state */
predicate AcceptorInit(a:Acceptor, id:Id) {
    && a.id == id
    && a.promised == Bottom
    && a.accepted == Nil
}

/* Acceptor next state */
predicate AcceptorNext(a:Acceptor, a':Acceptor, recvIo:Packet, sendIo:seq<Packet>) {
    && a'.id == a.id
    && match recvIo.msg {
        case Prepare(bal) => AcceptorNext_RcvPrepare(a, a', recvIo, sendIo)
        case Propose(bal, val) => AcceptorNext_RcvPropose(a, a', recvIo, sendIo)
        case _ => a == a' && sendIo == []
    }
}

/* Acceptor next state, process Prepare message */
predicate AcceptorNext_RcvPrepare(a:Acceptor, a':Acceptor, recvIo:Packet, sendIo:seq<Packet>) 
    requires recvIo.msg.Prepare?
{   
    if BalLt(a.promised, recvIo.msg.bal) then
        AcceptorPromise(a, a', recvIo, sendIo)
    else 
        AcceptorPreempt(a, a', recvIo, sendIo)
}

/* Acceptor next state, process Accept message */
predicate AcceptorNext_RcvPropose(a:Acceptor, a':Acceptor, recvIo:Packet, sendIo:seq<Packet>) 
    requires recvIo.msg.Propose?
{
    if BalLtEq(a.promised, recvIo.msg.bal)  then
        AcceptorAccept(a, a', recvIo, sendIo)
    else 
        AcceptorPreempt(a, a', recvIo, sendIo)
}

/* Acceptor send Promise */
predicate AcceptorPromise(a:Acceptor, a':Acceptor, recvIo:Packet, sendIo:seq<Packet>) 
    requires recvIo.msg.Prepare?
{
    && a'.promised == recvIo.msg.bal
    && a'.accepted == a.accepted
    && |sendIo| == 1
    && sendIo[0].src == a.id
    && sendIo[0].dst == recvIo.src
    && sendIo[0].msg == Promise(a.accepted)
}

/* Acceptor send Accept */
predicate AcceptorAccept(a:Acceptor, a':Acceptor, recvIo:Packet, sendIo:seq<Packet>) 
    requires recvIo.msg.Propose?
{
    && a'.promised == recvIo.msg.bal
    && a'.accepted == recvIo.msg.val
    && |sendIo| == 1
    && sendIo[0].src == a.id
    && sendIo[0].dst == recvIo.src
    && sendIo[0].msg == Accept()
}

/* Acceptor send Preempt */
predicate AcceptorPreempt(a:Acceptor, a':Acceptor, recvIo:Packet, sendIo:seq<Packet>) 
    requires recvIo.msg.Prepare? || recvIo.msg.Propose?
{
    && |sendIo| == 1
    && sendIo[0].src == a.id
    && sendIo[0].dst == recvIo.src
    && sendIo[0].msg == Preempt(a.promised, a.accepted)
}


/*****************************************************************************************
*                                 Leader State Machine                                   *
*****************************************************************************************/

datatype LeaderState = P1a | P1b | P2a | P2b

datatype Leader = Leader(
    id:Id,
    state:LeaderState,
    ballot:Ballot,
    val:Value
)

/* Leader initial state */
predicate LeaderInit(l:Leader, id:Id) {
    && l.id == id
    && l.state == P1a
    && l.ballot == Ballot(0, id.num)
    // value to propose is intentionally unspecified
}

}