from datatypes import *

AcceptorNext = Solver()

a = Const("a", Acceptor)
a_ = Const("a_", Acceptor)
recvIos = Const("recvIos", SeqSort(Packet))
sendIos = Const("sendIos", SeqSort(Packet))

AcceptorNext.add(Acceptor.consts(a) == Acceptor.consts(a_))
AcceptorNext.add(Length(recvIos) == 1)
# TODO
BalLt = And(
    Implies(
        Acceptor.promised(a) == Ballot.Bottom,
        Message.bal(Packet.msg(recvIos[0])) != Ballot.Bottom,
    ),
    Implies(
        Acceptor.promised(a) != Ballot.Bottom,
        If(Message.bal(Packet.msg(recvIos[0])) == Ballot.Bottom, False, If()),
    ),
)
# TODO
BalLtEq = Or()
# TODO
AcceptorPromise = Or()
# TODO
AcceptorPreempt = Or()

AcceptorNext_RcvPrepare = If(BalLt, AcceptorPromise, AcceptorPreempt)
AcceptorNext_RcvPropose = If(BalLtEq, AcceptorPromise, AcceptorPreempt)
AcceptorNext.add(
    Implies(
        Message.is_Prepare(Packet.msg(recvIos[0])),
        AcceptorNext_RcvPrepare,
    ),
    Implies(
        Message.is_Propose(Packet.msg(recvIos[0])),
        AcceptorNext_RcvPropose,
    ),
    Implies(
        And(
            Message.is_Prepare(Packet.msg(recvIos[0])),
            Message.is_Propose(Packet.msg(recvIos[0])),
        ),
        And(
            a == a_,
            Length(sendIos) == 0,
        ),
    ),
)
