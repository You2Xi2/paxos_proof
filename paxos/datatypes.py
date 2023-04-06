from z3 import *

# Id
agent = Datatype('agent')
agent.declare('Ldr')
agent.declare('Acc')
agent = agent.create()

Id = Datatype('Id')
Id.declare('Id', ('agt', agent), ('idx', IntSort()))
Id = Id.create()

# ValBal
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

# Acceptor
AcceptorConstants = Datatype('AcceptorConstants')
AcceptorConstants.declare('AConsts', ('id', Id))
AcceptorConstants = AcceptorConstants.create()

Acceptor = Datatype('Acceptor')
Acceptor.declare('Acceptor', ('consts', AcceptorConstants), ('promised', Ballot), ('accepted', ValBal))
Acceptor = Acceptor.create()

# Packet
Message = Datatype('Message')
Message.declare('Prepare', ('bal', Ballot))
Message.declare('Promise', ('bal', Ballot), ('vb', ValBal))
Message.declare('Propose', ('bal', Ballot), ('val', Value))
Message.declare('Accept', ('bal', Ballot), ('val', Value))
Message.declare('Preempt', ('bal', Ballot))
Message = Message.create()

Packet = Datatype('Packet')
Packet.declare('Packet', ('src', Id), ('dst', Id), ('msg', Message))
Packet = Packet.create()

Unit