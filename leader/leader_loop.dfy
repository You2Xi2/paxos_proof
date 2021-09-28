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
function NextIdx(c:Constants, idx:nat) : nat
  requires c.WF()
  requires c.ValidIdx(idx)
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
    && var dst_new_max := max(v.highest_heard[dst], message);
    // && v' == v.(highest_heard := v.highest_heard[dst := message])  // BUG: dst := dst_new_max
    && v' == v.(highest_heard := v.highest_heard[dst := dst_new_max])
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
// any seen is of existing ids? (this doesn't seem to matter for safety, since such a bogus seen cannot make anyone a leader)
// any seen is at least as big as the id before it.
// any id can't be seen east of a larger id.
    && ClockwiseInv(c, v)
    && LeaderHasLargestIdInv(c, v)
}
// Any ID can't be seen clockwise of a larget ID.
predicate ClockwiseInv(c:Constants, v:Variables)
    requires c.WF() && v.WF(c)
{
    forall i | c.ValidIdx(i) :: cwHelper(c, v, i)
}
predicate cwHelper(c:Constants, v:Variables, my_idx:nat) 
    requires c.WF() && v.WF(c)
    requires c.ValidIdx(my_idx)
{
    var my_id := c.ids[my_idx];
    forall other_idx:nat, k:nat |  
        && c.ValidIdx(other_idx) && c.ValidIdx(k)
        && c.ids[other_idx] > my_id 
        && (k > other_idx || k <= my_idx) 
        ::
        v.highest_heard[k] != my_id 
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
    forall k:nat | c.ValidIdx(k) :: c.ids[k] <= c.ids[i]
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
        assert Safety(c, v');
        CWInvNoLeader(c, v, v');
        assert Inv(c, v');
    } else {
        // Someone is the leader in state v
        assume false;
        assert Inv(c, v');
    }
}

lemma CWInvNoLeader(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires Safety(c, v')
    requires forall i | c.ValidIdx(i) :: !IsLeader(c, v, i)
    ensures ClockwiseInv(c, v')
{
    var step :| NextStep(c, v, v', step);
    var src := step.src;
    var dst := NextIdx(c, src);
    forall i | c.ValidIdx(i) 
    ensures cwHelper(c, v', i)
    {
        // This is the line the causes the Timeout
        var my_id := c.ids[i];
    }
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
