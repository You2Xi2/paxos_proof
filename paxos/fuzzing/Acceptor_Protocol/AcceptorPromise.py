from datatypes import *

AcceptorPromise = Solver()

a = Const('a', Acceptor)
a_ = Const('a_', Acceptor)
recvIo = Const('recvIo', Packet)
sendIos = [Const('sendIos_1', Packet)] # fixed size sequence for now
# Requires:
AcceptorPromise.add(Message.is_Prepare(Packet.msg(recvIo)))
# prepare message not bottom
# TODO
AcceptorPromise.add(Message.bal(Packet.msg(recvIo)) != Ballot.Bottom)
AcceptorPromise.add(Packet.msg(recvIo) != Message.Prepare(Ballot.Bottom))
# Acc
AcceptorPromise.add(Id.agt(AcceptorConstants.id(Acceptor.consts(a))) == agent.Acc)
# Ldr
AcceptorPromise.add(Id.agt(Packet.src(recvIo)) == agent.Ldr)

# Ensures:
AcceptorPromise.add(Acceptor.promised(a_) == Message.bal(Packet.msg(recvIo)))
AcceptorPromise.add(Acceptor.accepted(a) == Acceptor.accepted(a_))
AcceptorPromise.add(len(sendIos) == 1)
AcceptorPromise.add(Packet.src(sendIos[0]) == AcceptorConstants.id(Acceptor.consts(a)))
AcceptorPromise.add(Packet.dst(sendIos[0]) == Packet.src(recvIo))
AcceptorPromise.add(Packet.msg(sendIos[0]) == Message.Promise(Message.bal(Packet.msg(recvIo)), Acceptor.accepted(a)))
# acceptor consts should not change
AcceptorPromise.add(Acceptor.consts(a) == Acceptor.consts(a_))
# the message should be to myself
AcceptorPromise.add(Packet.dst(recvIo) == AcceptorConstants.id(Acceptor.consts(a)))

for i in range(1):
    if AcceptorPromise.check() == sat:
        print("Found a solution in %d iteration." % i)
        m = AcceptorPromise.model()
        # print(m.evaluate(Packet.msg(recvIo), model_completion=True))
        # print(m.evaluate(Message.bal(Packet.msg(recvIo))))

        print(m.evaluate(a, model_completion=True))
        print(m.evaluate(a_, model_completion=True))
        print("recvIo: ", m.evaluate(recvIo, model_completion=True))
        print("sendIo: ", m.evaluate(sendIos[0], model_completion=True))
        AcceptorPromise.add(a == m.evaluate(a))
        AcceptorPromise.add(recvIo != m.evaluate(recvIo))
    else:
        print("The spec is unrealistic in %d iteration." % i)
