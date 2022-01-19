include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"
include "proof_agreement_invariants.dfy"

module Proof_Axioms {
import opened Network
import opened Agents
import opened Types
import opened Synod
import opened Proof_Agreement_Invs

lemma {:axiom} axiom_BallotInduction1(c:Constants, ds:DistrSys, accpt:Packet, b:Ballot, v:Value) 
    requires c.WF() && ds.WF(c)
    requires isAcceptPkt(ds, accpt)
    requires BalLtEq(b, accpt.msg.bal)
    requires accpt.msg.bal == b ==>  accpt.msg.val == v
    requires BalLt(b, accpt.msg.bal) ==> 
        (exists accpt2:Packet :: 
            && isAcceptPkt(ds, accpt2) 
            && BalLtEq(b, accpt2.msg.bal) && BalLt(accpt2.msg.bal, accpt.msg.bal)
            && accpt2.msg.val == accpt.msg.val)
    ensures accpt.msg.val == v


lemma {:axiom} axiom_Set_Cover<T>(S1:set<T>, S2:set<T>, U:set<T>)
    requires S1 <= U 
    requires S2 <= U
    requires S1 * S2 == {}
    requires |S1| + |S2| >= |U|
    ensures S1 + S2 == U


lemma {:axiom} axiom_Set_DisjointSets<T>(S1:set<T>, S2:set<T>)
    requires forall e | e in S1 :: e !in S2
    ensures S1 * S2 == {}


lemma {:axiom} axiom_Set_Intersection(S1:set<Id>, S2:set<Id>, U:set<Id>) returns (e:Id)
    requires |S1| > |U|/2
    requires |S2| > |U|/2
    requires forall id | id in S1 :: id in U
    requires forall id | id in S2 :: id in U
    ensures e in U && e in S1 && e in S2

}