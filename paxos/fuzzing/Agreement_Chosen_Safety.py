from datatypes import *

solver = Solver()

c = Const("c", Constants)
ds = Const("ds", DistrSys)

f = Constants.f(c)
ldr_ids = Constants.ldr_ids(c)
ldr_vals = Constants.ldr_vals(c)
acc_ids = Constants.acc_ids(c)

i = Int("i")

ValidLdrIdx = Function("ValidLdrIdx", IntSort(), BoolSort())
solver.add(ValidLdrIdx(i) == And(0 <= i, i < Length(ldr_ids)))

ValidAccIdx = Function("ValidAccIdx", IntSort(), BoolSort())
solver.add(ValidAccIdx(i) == And(0 <= i, i < Length(acc_ids)))

ValidLdrVals = And(
    Length(ldr_vals) == Length(ldr_ids),
    ForAll(
        [i],
        Implies(ValidLdrIdx(i), Not(Value.is_Nil(ldr_vals[i]))),
    ),
)

ValidTypes = And(
    ForAll(
        [i],
        Implies(ValidLdrIdx(i), agent.is_Ldr(Id.agt(ldr_ids[i]))),
    ),
    ForAll(
        [i],
        Implies(ValidLdrIdx(i), agent.is_Acc(Id.agt(acc_ids[i]))),
    ),
)

ValidIds = And(
    ForAll(
        [i],
        Implies(ValidLdrIdx(i), Id.idx(ldr_ids[i]) == i),
    ),
    ForAll(
        [i],
        Implies(ValidAccIdx(i), Id.idx(acc_ids[i]) == i),
    ),
)

j = Int("j")
UniqueIds = And(
    ForAll(
        [i, j],
        Implies(
            And(
                ValidLdrIdx(i),
                ValidLdrIdx(j),
                ldr_ids[i] == ldr_ids[j],
            ),
            i == j,
        ),
    ),
    ForAll(
        [i, j],
        Implies(
            And(
                ValidAccIdx(i),
                ValidAccIdx(j),
                acc_ids[i] == acc_ids[j],
            ),
            i == j,
        ),
    ),
)

c_WF = And(
    f >= 1,
    Length(ldr_ids) >= 1,
    Length(acc_ids) == 2 * f + 1,
    ValidLdrVals,
    ValidTypes,
    ValidIds,
    UniqueIds,
)

network = DistrSys.network(ds)
leaders = DistrSys.leaders(ds)
acceptors = DistrSys.acceptors(ds)

ds_WF = And(
    c_WF,
    Length(leaders) == Length(ldr_ids),
    Length(acceptors) == Length(acc_ids),
    # (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.id == c.ldr_ids[i])
    ForAll(
        [i],
        Implies(
            ValidLdrIdx(i),
            LeaderConstants.id(Leader.consts(leaders[i])) == ldr_ids[i],
        ),
    ),
    # (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.initval == c.ldr_vals[i])
    ForAll(
        [i],
        Implies(
            ValidLdrIdx(i),
            LeaderConstants.initval(Leader.consts(leaders[i])) == ldr_vals[i],
        ),
    ),
    # (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.accConf == c.acc_ids)
    ForAll(
        [i],
        Implies(
            ValidLdrIdx(i),
            LeaderConstants.accConf(Leader.consts(leaders[i])) == acc_ids,
        ),
    ),
    # (forall i | c.ValidLdrIdx(i) :: leaders[i].consts.f == c.f)
    ForAll(
        [i],
        Implies(
            ValidLdrIdx(i),
            LeaderConstants.f(Leader.consts(leaders[i])) == f,
        ),
    ),
    # (forall i | c.ValidAccIdx(i) :: acceptors[i].consts.id == c.acc_ids[i])
    ForAll(
        [i],
        Implies(
            ValidAccIdx(i),
            AcceptorConstants.id(Acceptor.consts(acceptors[i])) == acc_ids[i],
        ),
    ),
)


# ValidLeaderSource = Function(
#     "ValidLeaderSource", Constants, DistrSys, Packet, BoolSort()
# )
# solver.add(
#     ValidLeaderSource(c, ds, p)
#     == And(
#         agent.is_Ldr(Id.agt(Packet.src(p))), ValidLdrIdx(Id.idx(Packet.src(p)))
#     )
# )
def ValidLeaderSource(c, ds, p):
    return And(
        agent.is_Ldr(Id.agt(Packet.src(p))), ValidLdrIdx(Id.idx(Packet.src(p)))
    )


# ValidAcceptorDest = Function(
#     "ValidAcceptorDest", Constants, DistrSys, Packet, BoolSort()
# )
# solver.add(
#     ValidAcceptorDest(c, ds, p)
#     == And(
#         agent.is_Acc(Id.agt(Packet.dst(p))), ValidAccIdx(Id.idx(Packet.dst(p)))
#     )
# )
def ValidAcceptorDest(c, ds, p):
    return And(
        agent.is_Acc(Id.agt(Packet.dst(p))), ValidAccIdx(Id.idx(Packet.dst(p)))
    )


# ValidAcceptorSource = Function(
#     "ValidAcceptorSource", Constants, DistrSys, Packet, BoolSort()
# )
# solver.add(
#     ValidAcceptorSource(c, ds, p)
#     == ValidAcceptorSource(c, ds, p)
#     == And(
#         agent.is_Acc(Id.agt(Packet.src(p))), ValidAccIdx(Id.idx(Packet.src(p)))
#     )
# )
def ValidAcceptorSource(c, ds, p):
    return And(
        agent.is_Acc(Id.agt(Packet.src(p))), ValidAccIdx(Id.idx(Packet.src(p)))
    )


# ValidLeaderDest = Function(
#     "ValidLeaderDest", Constants, DistrSys, Packet, BoolSort()
# )
# solver.add(
#     ValidLeaderDest(c, ds, p)
#     == And(
#         agent.is_Ldr(Id.agt(Packet.dst(p))), ValidLdrIdx(Id.idx(Packet.dst(p)))
#     )
# )
def ValidLeaderDest(c, ds, p):
    return And(
        agent.is_Ldr(Id.agt(Packet.dst(p))), ValidLdrIdx(Id.idx(Packet.dst(p)))
    )


# p = Consts("p", Packet)
# ValidPacketSourceDest = Function(
#     "ValidPacketSourceDest", Constants, DistrSys, Packet, BoolSort()
# )
# solver.add(
#     And(
#         Implies(
#             Message.is_Prepare(Packet.msg(p)),
#             ValidPacketSourceDest(c, ds, p)
#             == And(ValidLeaderSource(c, ds, p), ValidAcceptorDest(c, ds, p)),
#         ),
#         Implies(
#             Message.is_Promise(Packet.msg(p)),
#             ValidPacketSourceDest(c, ds, p)
#             == And(ValidAcceptorSource(c, ds, p), ValidLeaderDest(c, ds, p)),
#         ),
#         Implies(
#             Message.is_Propose(Packet.msg(p)),
#             ValidPacketSourceDest(c, ds, p)
#             == And(ValidLeaderSource(c, ds, p), ValidAcceptorDest(c, ds, p)),
#         ),
#         Implies(
#             Message.is_Accept(Packet.msg(p)),
#             ValidPacketSourceDest(c, ds, p)
#             == And(ValidAcceptorSource(c, ds, p), ValidLeaderDest(c, ds, p)),
#         ),
#         Implies(
#             Message.is_Preempt(Packet.msg(p)),
#             ValidPacketSourceDest(c, ds, p)
#             == And(ValidAcceptorSource(c, ds, p), ValidLeaderDest(c, ds, p)),
#         ),
#     )
# )
def ValidPacketSourceDest(c, ds, p):
    return And(
        Implies(
            Message.is_Prepare(Packet.msg(p)),
            And(ValidLeaderSource(c, ds, p), ValidAcceptorDest(c, ds, p)),
        ),
        Implies(
            Message.is_Promise(Packet.msg(p)),
            And(ValidAcceptorSource(c, ds, p), ValidLeaderDest(c, ds, p)),
        ),
        Implies(
            Message.is_Propose(Packet.msg(p)),
            And(ValidLeaderSource(c, ds, p), ValidAcceptorDest(c, ds, p)),
        ),
        Implies(
            Message.is_Accept(Packet.msg(p)),
            And(ValidAcceptorSource(c, ds, p), ValidLeaderDest(c, ds, p)),
        ),
        Implies(
            Message.is_Preempt(Packet.msg(p)),
            And(ValidAcceptorSource(c, ds, p), ValidLeaderDest(c, ds, p)),
        ),
    )


sentPackets = Environment.sentPackets(network)
AllPacketsValid = And(
    c_WF,
    ds_WF,
    # forall p | p in ds.network.sentPackets :: ValidPacketSourceDest(c, ds, p)
    ForAll(
        [i],
        Implies(
            And(0 <= i, i < Length(sentPackets)),
            ValidPacketSourceDest(c, ds, sentPackets[i]),
        ),
    ),
)

requires = And(c_WF, ds_WF, AllPacketsValid)


def isAcceptPkt(ds, p):
    return Exists(
        [i],
        And(0 <= i, i < Length(sentPackets), Message.is_Accept(Packet.msg(p))),
    )


def UniqueSources(qrm):
    # forall p1, p2 | p1 in qrm && p2 in qrm :: p1.src == p2.src ==> p1 == p2
    return ForAll(
        [i, j],
        Implies(
            And(0 <= i, i < Length(qrm), 0 <= j, j < Length(qrm)),
            Implies(Packet.src(qrm[i]) == Packet.src(qrm[j]), i == j),
        ),
    )


def SetOfAcceptMsgs(c, ds, S, b):
    # ignore requires as the caller satisfies it
    return And(
        UniqueSources(S),
        ForAll(
            [i],
            Implies(
                And(0 <= i, i < Length(S)),
                And(isAcceptPkt(ds, S[i]), Message.bal(Packet.msg(S[i])) == b),
            ),
        ),
    )


def QuorumOfAcceptMsgs(c, ds, qrm, b):
    # ignore requires as the caller satisfies it
    return And(Length(qrm) >= f + 1, SetOfAcceptMsgs(c, ds, qrm, b))


def AccPacketsHaveValueV(S, v):
    return And(
        # requires forall p | p in S :: p.msg.Accept?
        # forall p:Packet | p in S :: p.msg.val == v
        ForAll(
            [i],
            Implies(
                And(0 <= i, i < Length(S)),
                And(
                    Message.is_Accept(Packet.msg(S[i])),
                    Message.val(Packet.msg(S[i])) == v,
                ),
            ),
        ),
    )


qrm = Const("qrm", SeqSort(Packet))


def Chosen(c, ds, b, v):
    # ignore requires as the caller satisfies it
    return Exists(
        qrm,
        And(
            QuorumOfAcceptMsgs(c, ds, qrm, b),
            AccPacketsHaveValueV(qrm, v),
        ),
    )


b1, b2 = Consts("b1 b2", Ballot)
v1, v2 = Consts("v1 v2", Value)

Agreement_Chosen_Safety = ForAll(
    [b1, b2, v1, v2],
    Implies(
        And(
            Chosen(c, ds, b1, v1),
            Chosen(c, ds, b2, v2),
        ),
        v1 == v2,
    ),
)

solver.add(And(requires, Agreement_Chosen_Safety))

for i in range(1):
    if solver.check() == sat:
        print("Found a solution in %d iteration." % i)
        m = solver.model()

        print(m.evaluate(c, model_completion=True))
        print(m.evaluate(ds, model_completion=True))

        print("c: ", m.evaluate(c, model_completion=True))
        print("ds: ", m.evaluate(ds, model_completion=True))

        solver.add(c == m.evaluate(c))
        solver.add(ds != m.evaluate(ds))
    else:
        print("The spec is unrealistic in %d iteration." % i)
