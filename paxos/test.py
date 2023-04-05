from z3 import *

agent = Datatype('agent')
agent.declare('Ldr')
agent.declare('Acc')
agent = agent.create()

Id = Datatype('Id')
Id.declare('Id', ('agt', agent), ('idx', IntSort()))
Id = Id.create()

Value = Datatype('Value')
Value.declare('V', ('val', IntSort()))
Value.declare('Nil')
Value = Value.create()

Ballot = Datatype('Ballot')
Ballot.declare('Bottom')
Ballot.declare('Ballot', ('seqNo', IntSort()), ('idx', IntSort())) # nat for seqNo and idx
Ballot = Ballot.create()

ValBal = Datatype('ValBal')
ValBal.declare('VB', ('v', Value), ('b', Ballot))
ValBal = ValBal.create()

AcceptorConstants = Datatype('AcceptorConstants')
AcceptorConstants.declare('AConsts', ('id', Id))
AcceptorConstants = AcceptorConstants.create()

Acceptor = Datatype('Acceptor')
Acceptor.declare('Acceptor', ('consts', AcceptorConstants), ('promised', Ballot), ('accepted', ValBal))
Acceptor = Acceptor.create()

s = Solver()
a = Const('a', Acceptor)
print(type(a))
id = Const('id', Id)
# s.add(a.consts == AcceptorConstants.AConsts(id))
# s.check()


test = Datatype('test')
test.declare('x', ('value', IntSort()))
test = test.create()
solve(test.value == 2)

agent_instance = Const('agent_instance', agent)
solve(agent_instance != agent.Ldr)
# s.add(a.promised == Ballot.Bottom)
# s.add(a.accepted == )