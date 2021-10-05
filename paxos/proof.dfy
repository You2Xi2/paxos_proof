include "types.dfy"
include "network.dfy"
include "agents.dfy"
include "synod.dfy"

module Proof {
import opened Network
import opened Agents
import opened Types
import opened Synod


/* If all processes propose v, then every process that decides a value decides v */
predicate Validity(ds:DistrSys) {
    (exists v :: AllProcessesProposeV(ds, v)) 
    ==> 
    (exists v :: AllProcessesProposeV(ds, v) && AllDecidedProcessesDecidesV(ds, v)) 
}

predicate AllProcessesProposeV(ds:DistrSys, v:Value) {
    forall l | l in ds.leaders :: l.consts.initval == v
}

predicate AllDecidedProcessesDecidesV(ds:DistrSys, v:Value){
    forall l | l in ds.leaders && l.state == Decided :: l.val == v
}


predicate Validity_Inv(ds:DistrSys) {
    && Validity(ds)
}


lemma InitImpliesInv(c:Constants, ds:DistrSys) 
    requires Init(c, ds)
    ensures Validity_Inv(ds)
{}

lemma NextPreservesInv(c:Constants, ds:DistrSys, ds':DistrSys) 
    requires Validity_Inv(ds)
    requires Next(c, ds, ds')
    ensures Validity_Inv(ds')
{
    // TODO
    assume false;
}



}