from z3 import *

# Id
agent = Datatype("agent")
agent.declare("Acc")
agent.declare("Ldr")
agent = agent.create()

Id = Datatype("Id")
Id.declare("Id", ("agt", agent), ("idx", IntSort()))
Id = Id.create()

# ValBal
Value = Datatype("Value")
Value.declare("V", ("val", IntSort()))
Value.declare("Nil")
Value = Value.create()

Ballot = Datatype("Ballot")
Ballot.declare("Bottom")
Ballot.declare(
    "Ballot", ("seqNo", IntSort()), ("idx", IntSort())
)  # nat for seqNo and idx
Ballot = Ballot.create()

ValBal = Datatype("ValBal")
ValBal.declare("VB", ("v", Value), ("b", Ballot))
ValBal = ValBal.create()

# Acceptor
AcceptorConstants = Datatype("AcceptorConstants")
AcceptorConstants.declare("AConsts", ("id", Id))
AcceptorConstants = AcceptorConstants.create()

Acceptor = Datatype("Acceptor")
Acceptor.declare(
    "Acceptor",
    ("consts", AcceptorConstants),
    ("promised", Ballot),
    ("accepted", ValBal),
)
Acceptor = Acceptor.create()

# Packet
Message = Datatype("Message")
Message.declare("Prepare", ("bal", Ballot))
Message.declare("Promise", ("bal", Ballot), ("vb", ValBal))
Message.declare("Propose", ("bal", Ballot), ("val", Value))
Message.declare("Accept", ("bal", Ballot), ("val", Value))
Message.declare("Preempt", ("bal", Ballot))
Message = Message.create()

Packet = Datatype("Packet")
Packet.declare("Packet", ("src", Id), ("dst", Id), ("msg", Message))
Packet = Packet.create()

# Leader
LeaderConstants = Datatype("LeaderConstants")
LeaderConstants.declare(
    "LConsts",
    ("id", Id),
    ("accConf", SeqSort(Id)),
    ("f", IntSort()),
    ("initval", Value),
)
LeaderConstants = LeaderConstants.create()

LeaderState = Datatype("LeaderState")
LeaderState.declare("P1a")
LeaderState.declare("P1b")
LeaderState.declare("P2a")
LeaderState.declare("P2b")
LeaderState.declare("Decided")
LeaderState = LeaderState.create()

Leader = Datatype("Leader")
Leader.declare(
    "Leader",
    ("consts", LeaderConstants),
    ("state", LeaderState),
    ("ballot", Ballot),
    ("val", Value),
    ("promises", SetSort(Packet)),
    ("accepts", SetSort(Id)),
)
Leader = Leader.create()

# Constants
Constants = Datatype("Constants")
Constants.declare(
    "Constants",
    ("f", IntSort()),
    ("ldr_ids", SeqSort(Id)),
    ("ldr_vals", SeqSort(Value)),
    ("acc_ids", SeqSort(Id)),
)
Constants = Constants.create()

# EnvStep
EnvStep = Datatype("EnvStep")
EnvStep.declare(
    "IoStep",
    ("actor", Id),
    ("recvIos", SeqSort(Packet)),
    ("sendIos", SeqSort(Packet)),
)
EnvStep = EnvStep.create()

# Environment
Environment = Datatype("Environment")
Environment.declare(
    "Env",
    ("sentPackets", SeqSort(Packet)),
    ("nextStep", EnvStep),
)
Environment = Environment.create()

# DistrSys
DistrSys = Datatype("DistrSys")
DistrSys.declare(
    "DistrSys",
    ("network", Environment),
    ("leaders", SeqSort(Leader)),
    ("acceptors", SeqSort(Acceptor)),
)
DistrSys = DistrSys.create()
