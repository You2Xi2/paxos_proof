from datatypes import *

c = Const("c", Constants)
ds = Const("ds", DistrSys)

f = Constants.f(c)
ldr_ids = Constants.ldr_ids(c)
ldr_vals = Constants.ldr_vals(c)
acc_ids = Constants.acc_ids(c)

i = Int("i")
j = Int("j")


def ValidLdrIdx(i):
    return And(0 <= i, i < Length(ldr_ids))


def ValidAccIdx(i):
    return And(0 <= i, i < Length(acc_ids))


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
        Implies(ValidAccIdx(i), agent.is_Acc(Id.agt(acc_ids[i]))),
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
    # c_WF,  # requires
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

# requires for Validity, AllProcessesInitV, AllDecidedProcessesDecidesV
requires = And(c_WF, ds_WF)

v = Const("v", Value)
b = Const("b", Ballot)

AllProcessesInitV = ForAll([i], Implies(ValidLdrIdx(i), ldr_vals[i] == v))

AllDecidedProcessesDecidesV = ForAll(
    [i],
    Implies(
        And(
            i >= 0,
            i < Length(leaders),
            # LeaderState.is_Decided(Leader.state(leaders[i])),
        ),
        Leader.val(leaders[i]) == v,
    ),
)


Validity = Implies(AllProcessesInitV, AllDecidedProcessesDecidesV)

ExistDecided = And(
    Length(leaders) >= 5,
    LeaderState.is_Decided(Leader.state(leaders[1])),
    LeaderState.is_Decided(Leader.state(leaders[3])),
)


solver = Solver()
solver.add(requires)
# solver.add(AllProcessesInitV)
# solver.add(AllDecidedProcessesDecidesV)
solver.add(Validity)

for i in range(2):
    if solver.check() == sat:
        print("Found a solution in %d iteration." % i)
        m = solver.model()

        print("c: ", m.evaluate(c, model_completion=True))
        print("ds: ", m.evaluate(ds, model_completion=True))
        print("v: ", m.evaluate(v, model_completion=True))
        print("leaders: ", m.evaluate(leaders, model_completion=True))

        solver.add(c != m.evaluate(c))
        solver.add(ds != m.evaluate(ds))
        solver.add(ExistDecided)
    else:
        print("The spec is unrealistic in %d iteration." % i)
        print(solver.unsat_core())

# Summary: the spec is overconstrained by removing line 152
# it's hard to tell it's buggy by manually check the output
# because there are still correct outputs
