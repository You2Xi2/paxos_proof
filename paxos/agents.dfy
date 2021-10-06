include "types.dfy"

module Agents {
import opened Types


/*****************************************************************************************
*                                Acceptor State Machine                                  *
*****************************************************************************************/

datatype AcceptorConstants = AConsts(id:Id)

datatype Acceptor = Acceptor(
    consts:AcceptorConstants, 
    promised:Ballot, 
    accepted:Value)

/* Acceptor initial state */
predicate AcceptorInit(a:Acceptor, id:Id) {
    && a.consts == AConsts(id)
    && a.promised == Bottom
    && a.accepted == Nil
}

/* Acceptor next state */
predicate AcceptorNext(a:Acceptor, a':Acceptor, recvIos:seq<Packet>, sendIo:seq<Packet>) {
    && a'.consts == a.consts
    && |recvIos| == 1
    && match recvIos[0].msg {
        case Prepare(bal) => AcceptorNext_RcvPrepare(a, a', recvIos[0], sendIo)
        case Propose(bal, val) => AcceptorNext_RcvPropose(a, a', recvIos[0], sendIo)
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
predicate AcceptorNext_RcvPropose(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Propose?
{
    if BalLtEq(a.promised, recvIo.msg.bal)  then
        AcceptorAccept(a, a', recvIo, sendIos)
    else 
        AcceptorPreempt(a, a', recvIo, sendIos)
}

/* Acceptor send Promise */
predicate AcceptorPromise(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Prepare?
{
    && a'.promised == recvIo.msg.bal
    && a'.accepted == a.accepted
    && |sendIos| == 1
    && sendIos[0].src == a.consts.id
    && sendIos[0].dst == recvIo.src
    && sendIos[0].msg == Promise(a.promised, a.accepted)
}

/* Acceptor send Accept */
predicate AcceptorAccept(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Propose?
{
    && a'.promised == recvIo.msg.bal
    && a'.accepted == recvIo.msg.val
    && |sendIos| == 1
    && sendIos[0].src == a.consts.id
    && sendIos[0].dst == recvIo.src
    && sendIos[0].msg == Accept(recvIo.msg.bal)
}

/* Acceptor send Preempt */
predicate AcceptorPreempt(a:Acceptor, a':Acceptor, recvIo:Packet, sendIos:seq<Packet>) 
    requires recvIo.msg.Prepare? || recvIo.msg.Propose?
{
    && |sendIos| == 1
    && sendIos[0].src == a.consts.id
    && sendIos[0].dst == recvIo.src
    && sendIos[0].msg == Preempt(a.promised, a.accepted)
    && a'.promised == a.promised
    && a'.accepted == a.accepted
    // Bug 1: a'.promised and a'.accepted unspecified
}


/*****************************************************************************************
*                                 Leader State Machine                                   *
*****************************************************************************************/

datatype LeaderState = P1a | P1b | P2a | P2b | Decided
datatype LeaderConstants = LConsts(id:Id, accConf:seq<Id>, f:nat, initval:Value)

datatype Leader = Leader(
    consts:LeaderConstants,    
    state:LeaderState,
    ballot:Ballot,
    val:Value,
    promises:set<Id>,
    accepts:set<Id>
)

/* Leader initial state */
predicate LeaderInit(l:Leader, id:Id, accConf:seq<Id>, f:nat, initval:Value) {
    && l.consts == LConsts(id, accConf, f, initval)
    && l.state == P1a
    && l.ballot == Ballot(0, id.idx)
    && l.val == initval
}

/* Leader next state */
predicate LeaderNext(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) {
    && l'.consts == l.consts
    && match l.state {
        case P1a => LeaderNext_P1a(l, l', recvIos, sendIos)
        case P1b => LeaderNext_P1b(l, l', recvIos, sendIos)
        case P2a => LeaderNext_P2a(l, l', recvIos, sendIos)
        case P2b => LeaderNext_P2b(l, l', recvIos, sendIos)
        case Decided => LeaderStutter(l, l', sendIos)
    }
}


/* Leader next state, broadcast Prepare messages */
predicate LeaderNext_P1a(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P1a
{
    && l'.state == P1b
    && l'.ballot == l.ballot
    && l'.val == l.val
    && l'.promises == l.promises
    && l'.accepts == l.accepts
    && recvIos == []
    && LeaderSendPrepare(l, sendIos)
}

predicate LeaderSendPrepare(l:Leader, sendIos:seq<Packet>) {
    && |sendIos| == |l.consts.accConf|
    && forall i | 0 <= i < |sendIos| 
        :: sendIos[i] == Packet(l.consts.id, l.consts.accConf[i], Prepare(l.ballot))
}


/* Leader next state, wait for quorum of Promise messages */
predicate LeaderNext_P1b(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P1b
{
    && |recvIos| == 1 
    && match recvIos[0].msg {
        case Prepare(bal) => LeaderStutter(l, l', sendIos)
        case Promise(bal, val) => LeaderProcessPromise(l, l', recvIos[0], sendIos)
        case Propose(bal, val) => LeaderStutter(l, l', sendIos)
        case Accept(bal) =>  LeaderStutter(l, l', sendIos)
        case Preempt(bal, val) => LeaderProcessPreempt(l, l', recvIos[0].msg, sendIos)
    }
}

predicate LeaderStutter(l:Leader, l':Leader, sendIos:seq<Packet>) {
    l' == l && sendIos == []
}

predicate LeaderProcessPromise(l:Leader, l':Leader, pkt:Packet, sendIos:seq<Packet>) 
    requires pkt.msg.Promise?
    requires l.state == P1b
{
    var src, msg := pkt.src, pkt.msg;
    if msg.bal == l.ballot && src !in l.promises then
        LeaderProcessValidPromise(l, l', src, msg, sendIos)
    else 
        // This is a stale promise
        LeaderStutter(l, l', sendIos)
}

predicate LeaderProcessValidPromise(l:Leader, l':Leader, src:Id, msg:Message, sendIos:seq<Packet>) 
    requires msg.Promise?
    requires l.state == P1b
{
    && sendIos == []    // Bug 2: left out this line, so sendIos was unspecified
    && if |l.promises| == 2*l.consts.f then 
        // Go to phase 2a
        && l'.state == P2a
        && l'.ballot == l.ballot
        && l'.val == (if msg.val == Nil then l.val else msg.val)
        && l'.promises == {}
        && l'.accepts == {}
    else 
        && l'.state == l.state
        && l'.ballot == l.ballot
        && l'.val == (if msg.val == Nil then l.val else msg.val)
        && l'.promises == l.promises + {src}
        && l'.accepts == l.accepts
}

predicate LeaderProcessPreempt(l:Leader, l':Leader, msg:Message, sendIos:seq<Packet>) 
    requires msg.Preempt?
{
    && sendIos == []    // Bug 2: left out this line, so sendIos was unspecified
    && if BalLt(l.ballot, msg.bal) then 
        // I am preempted
        && l'.state == P1a
        && l'.ballot == NextBallot(msg.bal, l.consts.id.idx)
        && l'.promises == {}
        && l'.accepts == {}
        && if msg.val == Nil 
            then l'.val == l.val
            else l'.val == msg.val
    else 
        // False alarm, msg is stale
        LeaderStutter(l, l', sendIos)
}


/* Leader next state, broadcast Propose messages */
predicate LeaderNext_P2a(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P2a
{
    && l'.state == P2b
    && l'.ballot == l.ballot
    && l'.val == l.val
    && l'.promises == l.promises
    && l'.accepts == l.accepts
    && recvIos == []
    && LeaderSendPropose(l, sendIos)
}

predicate LeaderSendPropose(l:Leader, sendIos:seq<Packet>) 
    requires l.state == P2a
{
    && |sendIos| == |l.consts.accConf|
    && forall i | 0 <= i < |sendIos| 
        :: sendIos[i] == Packet(l.consts.id, l.consts.accConf[i], Propose(l.ballot, l.val))
}


/* Leader next state, wait for quorum of Accept messages */
predicate LeaderNext_P2b(l:Leader, l':Leader, recvIos:seq<Packet>, sendIos:seq<Packet>) 
    requires l.state == P2b
{
    && |recvIos| == 1 
    && match recvIos[0].msg {
        case Prepare(bal) => LeaderStutter(l, l', sendIos)
        case Promise(bal, val) => LeaderStutter(l, l', sendIos)
        case Propose(bal, val) => LeaderStutter(l, l', sendIos)
        case Accept(bal) =>  LeaderProcessAccept(l, l', recvIos[0], sendIos)
        case Preempt(bal, val) => LeaderProcessPreempt(l, l', recvIos[0].msg, sendIos)
    }
}

predicate LeaderProcessAccept(l:Leader, l':Leader, pkt:Packet, sendIos:seq<Packet>) 
    requires pkt.msg.Accept?
    requires l.state == P2b
{
    var src, msg := pkt.src, pkt.msg;
    if msg.bal == l.ballot && src !in l.accepts then
        LeaderProcessValidAccept(l, l', src, msg, sendIos)
    else 
        // This is a stale Accept
        LeaderStutter(l, l', sendIos)
}

predicate LeaderProcessValidAccept(l:Leader, l':Leader, src:Id, msg:Message, sendIos:seq<Packet>) 
    requires msg.Accept?
    requires l.state == P2b
{
    if |l.accepts| == 2*l.consts.f then 
        // Go to Decided state
        && l'.state == Decided
        && l'.ballot == l.ballot
        && l'.val == l.val
        && l'.promises == l.promises
        && l'.accepts == l.accepts
    else 
        && l'.state == l.state
        && l'.ballot == l.ballot
        && l'.val == l.val
        && l'.promises == l.promises
        && l'.accepts == l.accepts + {src}
}
}