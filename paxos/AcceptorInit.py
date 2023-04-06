from datatypes import *
AcceptorInit = Solver()
a = Const('a', Acceptor)
id = Const('id', Id)
# AcceptorInit.add(Id.agt(id) == agent.Acc)
AcceptorInit.add(Acceptor.consts(a) == AcceptorConstants.AConsts(id))
AcceptorInit.add(Acceptor.promised(a) == Ballot.Bottom)
AcceptorInit.add(Acceptor.accepted(a) == ValBal.VB(Value.Nil, Ballot.Bottom))
for i in range(10):
    if AcceptorInit.check() == sat:
        print("Found a solution in %d th iteration." % i)
        m = AcceptorInit.model()
        print(m.evaluate(id, model_completion=True))
        print(m.evaluate(a, model_completion=True))
        AcceptorInit.add(id != m.evaluate(id))
        # if only one parameter changes, fix it
        # AcceptorInit.add(Id.idx(id) == m.evaluate(Id.idx(id)))
    else:
        print("The spec is unrealistic in %d th iteration." % i)
        break

