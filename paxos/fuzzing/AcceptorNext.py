from datatypes import *

AcceptorNext = Solver()

a = Const("a", Acceptor)
a_ = Const("a_", Acceptor)
recvIos = Const("recvIos", SeqSort(Packet))
sendIos = Const("sendIos", SeqSort(Packet))

AcceptorNext.add(Acceptor.consts(a) == Acceptor.consts(a_))
AcceptorNext.add(Length(recvIos) == 1)

recvIo = recvIos[0]
b1 = Acceptor.promised(a)
b2 = Message.bal(Packet.msg(recvIo))

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

BalLtEq = Or(b1 == b2, BalLt)

AcceptorPromise = And(
    Acceptor.promised(a_) == Message.bal(Packet.msg(recvIo)),
    Acceptor.accepted(a) == Acceptor.accepted(a_),
    Length(sendIos) == 1,
    Packet.src(sendIos[0]) == AcceptorConstants.id(Acceptor.consts(a)),
    Packet.dst(sendIos[0]) == Packet.src(recvIo),
    Packet.msg(sendIos[0])
    == Message.Promise(Message.bal(Packet.msg(recvIo)), Acceptor.accepted(a)),
    Acceptor.consts(a) == Acceptor.consts(a_),
    Packet.dst(recvIo) == AcceptorConstants.id(Acceptor.consts(a)),
)

AcceptorPreempt = And(
    Length(sendIos) == 1,
    Packet.src(sendIos[0]) == AcceptorConstants.id(Acceptor.consts(a)),
    Packet.dst(sendIos[0]) == Packet.src(recvIo),
    Packet.msg(sendIos[0]) == Message.Preempt(Acceptor.promised(a)),
    Acceptor.promised(a) == Acceptor.promised(a_),
    Acceptor.accepted(a) == Acceptor.accepted(a_),
)

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

for i in range(2):
    if AcceptorNext.check() == sat:
        print("Found a solution in %d iteration." % i)
        m = AcceptorNext.model()
        # print(m.evaluate(Packet.msg(recvIo), model_completion=True))
        # print(m.evaluate(Message.bal(Packet.msg(recvIo))))

        print(m.evaluate(a, model_completion=True))
        print(m.evaluate(a_, model_completion=True))

        print("recvIos: ", m.evaluate(recvIos, model_completion=True))
        print("sendIos: ", m.evaluate(sendIos, model_completion=True))

        AcceptorNext.add(a == m.evaluate(a))
        AcceptorNext.add(recvIos != m.evaluate(recvIos))
        AcceptorNext.add(sendIos != m.evaluate(sendIos))
    else:
        print("The spec is unrealistic in %d iteration." % i)
