from datatypes import *

AcceptorNext = Solver()

a = Const("a", Acceptor)
a_ = Const("a_", Acceptor)
recvIos = Const("recvIos", SeqSort(Packet))
sendIos = Const("sendIos", SeqSort(Packet))

AcceptorNext.add(Acceptor.consts(a) == Acceptor.consts(a_))
AcceptorNext.add(Length(recvIos) == 1)

b1 = Acceptor.promised(a)
b2 = Message.bal(Packet.msg(recvIos[0]))

BalLt = And(
    Implies(
        Ballot.is_Bottom(b1),
        Not(Ballot.is_Bottom(b2)),
    ),
    Implies(
        Ballot.is_Ballot(b1),
        If(
            Ballot.is_Bottom(b2),
            False,
            If(
                Ballot.seqNo(b1) != Ballot.seqNo(b2),
                Ballot.seqNo(b1) < Ballot.seqNo(b2),
                Ballot.idx(b1) < Ballot.idx(b2),
            ),
        ),
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
