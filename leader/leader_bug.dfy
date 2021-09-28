// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
    predicate ValidIdx(i: nat) {
        0<=i<|ids|
    }
    predicate UniqueIds() {
        (forall i:nat, j:nat | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
    } 
    predicate WF() {
        0 < |ids|
    }
}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>) {
    predicate WF(c: Constants)
        requires c.WF()
    {
        && |highest_heard| == |c.ids|
    }
}

predicate Init(c: Constants, v: Variables) {
    && c.WF()
    && c.UniqueIds()
    && v.WF(c)
    // Everyone begins having heard about nobody, not even themselves.
    && (forall i:nat | c.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a:nat, b:nat) : nat {
    if a > b then a else b
}

function NextIdx(c:Constants, idx:nat) : (n:nat)
  requires c.WF()
  requires c.ValidIdx(idx)
  ensures n == 0 || n == idx + 1
  ensures idx == |c.ids| - 1 <==> n == 0 
  ensures idx < |c.ids| - 1 <==> n == idx + 1
{
    (idx + 1) % |c.ids|
}

predicate Transmission(c: Constants, v: Variables, v': Variables, src: nat)
{
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && c.ValidIdx(src)
    // Neighbor address in ring.
    && var dst := NextIdx(c, src);
    // src sends the max of its highest_heard value and its own id.
    && var message := max(v.highest_heard[src], c.ids[src]);
    // dst only overwrites its highest_heard if the message is higher.
    // && var dst_new_max := max(v.highest_heard[dst], message);
    && v' == v.(highest_heard := v.highest_heard[dst := message]) 
    // && v' == v.(highest_heard := v.highest_heard[dst := dst_new_max])
}


datatype Step = TransmissionStep(src: nat)

predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step) {
    match step {
        case TransmissionStep(src) => Transmission(c, v, v', src)
    }
}

predicate Next(c: Constants, v: Variables, v': Variables) {
    exists step :: NextStep(c, v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////
predicate IsLeader(c: Constants, v: Variables, i: nat)
    requires c.WF()
    requires v.WF(c)
{
    // If the highest I hear is my own id, then I am the leader
    && c.ValidIdx(i)
    && v.highest_heard[i] == c.ids[i]  
}

predicate Safety(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
{
    forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////
predicate Inv(c: Constants, v: Variables)
{
    && c.WF()
    && v.WF(c)
    && Safety(c, v)
    && c.UniqueIds()
    && ClockwiseInv(c, v)
    && LeaderHasLargestIdInv(c, v)
}

// Any ID can't be seen clockwise of a larget ID.
predicate ClockwiseInv(c:Constants, v:Variables)
    requires c.WF() && v.WF(c)
{
    forall i | c.ValidIdx(i) :: ClockwiseInv_Id(c, v, i)
}

// ID can't be seen clockwise of a larget ID.
predicate ClockwiseInv_Id(c:Constants, v:Variables, my_idx:nat) 
    requires c.WF() && v.WF(c)
    requires c.ValidIdx(my_idx)
{
    var my_id := c.ids[my_idx];
    forall other_idx:nat | OtherHasLargerID(c, my_idx, other_idx)
    :: ClockwiseNodesId(c, v, my_idx, other_idx)
}

predicate OtherHasLargerID(c:Constants, my_idx:nat, other_idx:nat) 
    requires c.WF()
    requires c.ValidIdx(my_idx)
    ensures OtherHasLargerID(c, my_idx, other_idx) ==> other_idx != my_idx
{
    && c.ValidIdx(other_idx)
    && c.ids[other_idx] > c.ids[my_idx] 
}

predicate ClockwiseNodesId(c:Constants, v:Variables, my_idx:nat, other_idx:nat)
    requires c.WF() && v.WF(c)
    requires c.ValidIdx(my_idx) && c.ValidIdx(other_idx)
    // requires my_idx != other_idx
    // requires OtherHasLargerID(c, my_idx, other_idx)
{
    var my_id := c.ids[my_idx];
    if other_idx > my_idx then
        forall k:nat | c.ValidIdx(k) && after(my_idx, other_idx, k)
        :: v.highest_heard[k] != my_id 
    else 
        forall k:nat | c.ValidIdx(k) && before(my_idx, other_idx, k)
        :: v.highest_heard[k] != my_id 
}

predicate after(my_idx:nat, other_idx:nat, k:nat) {
    k > other_idx || k <= my_idx
}

predicate before(my_idx:nat, other_idx:nat, k:nat) {
    k > other_idx && k <= my_idx
}


// Leader has the largest ID
predicate LeaderHasLargestIdInv(c:Constants, v:Variables) 
    requires c.WF() && v.WF(c)
{
    forall l:nat | c.ValidIdx(l) && IsLeader(c, v, l) :: LargestId(c, v, l)
}

predicate LargestId(c:Constants, v:Variables, i:nat) 
    requires c.WF() && v.WF(c)
    requires c.ValidIdx(i)
{
    forall k:nat | c.ValidIdx(k) :: !OtherHasLargerID(c, i, k) 
}


lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
{
    assert Inv(c, v);
}


lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{
    if forall i | c.ValidIdx(i) :: !IsLeader(c, v, i) {
        // No one is the leader in state v
        NextPreservesInv_NoLeader(c, v, v');
        assert Inv(c, v');
    } else {
        // Someone is the leader in state v
        NextPreservesInv_Leader(c, v, v');
        assert Inv(c, v');
    }
}

lemma NextPreservesInv_NoLeader(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires Safety(c, v)
    requires forall i | c.ValidIdx(i) :: !IsLeader(c, v, i)
    ensures Inv(c, v');
{
    var step :| NextStep(c, v, v', step);
    var src := step.src;
    var dst := NextIdx(c, src);
    // Prove ClockwiseInv(c, v')
    forall idx:nat | c.ValidIdx(idx) 
    ensures ClockwiseInv_Id(c, v', idx)
    {
        if src == idx {
            /* If v.highest[idx] sees own id, then contradiction, since no leader.
            * Hence, if idx+1 sees anything in v', it can't be ids[idx] */
            if v.highest_heard[idx] == c.ids[idx] {
                assert IsLeader(c, v, idx);
                assert false;
            } else {
                // Where v.highest_heard[idx] != c.ids[idx]
                lemma_OnlyOneChange(c, v, v', idx, dst);
                forall other_idx:nat | OtherHasLargerID(c, idx, other_idx)
                ensures ClockwiseNodesId(c, v', idx, other_idx)
                {}
            }
        }
    }
    // Prove LeaderHasLargestIdInv(c, v')
    forall l:nat | c.ValidIdx(l) && IsLeader(c, v', l) 
    ensures LargestId(c, v', l)
    {}
}


lemma NextPreservesInv_Leader(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires Safety(c, v)
    requires exists l | c.ValidIdx(l) :: IsLeader(c, v, l)
    ensures Inv(c, v');
{
    assert ClockwiseInv(c, v');
    assert LeaderHasLargestIdInv(c, v');
    assert Safety(c, v');
}




lemma lemma_OnlyOneChange(c: Constants, v: Variables, v': Variables, src:nat, dst:nat)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidIdx(src) && c.ValidIdx(dst)
    requires dst == NextIdx(c, src)
    requires Transmission(c, v, v', src)
    ensures forall i:nat | c.ValidIdx(i) && i != dst :: v.highest_heard[i] == v'.highest_heard[i];
{}

lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
{
    assert Safety(c, v);
}
