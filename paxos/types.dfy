module Types {

datatype agent = Ldr | Acc

datatype Id = Id(agt:agent, num:nat)

datatype Value = V(val:int) | Nil
datatype Ballot = Ballot(seqNo:nat, num:nat) | Bottom

datatype Message = Prepare(bal:Ballot)
                | Promise(bal:Ballot, val:Value)
                | Propose(bal:Ballot, val:Value)
                | Accept(bal:Ballot)
                | Preempt(bal:Ballot, val:Value)

datatype Packet = Packet(src:Id, dst:Id, msg:Message)

/* True iff b1 < b2 */
predicate BalLt(b1:Ballot, b2:Ballot) {
    match b1 {
        case Bottom => b2.Bottom?
        case Ballot(seqNo, id) =>
            if b2.Bottom? then false else 
                if b1.seqNo != b2.seqNo then b1.seqNo < b2.seqNo 
                else b1.num < b2.num
    }
}

/* True iff b1 <= b2 */
predicate BalLtEq(b1:Ballot, b2:Ballot) {
    b1 == b2 || BalLt(b1, b2)
}

/* True iff b1 > b2 */
predicate BalGt(b1:Ballot, b2:Ballot) {
    !BalLtEq(b1, b2)
}

/* Returns the next largest ballot for non-Bottom ballots, belonging to a given leader num */
function {:opaque} NextBallot(b:Ballot, num:nat) : (b':Ballot) 
    ensures b != Bottom ==> b' != Bottom
    ensures b != Bottom ==> BalGt(b', b)
    ensures b != Bottom ==> b'.num == num
{
    if b == Bottom then Bottom
    else Ballot(b.seqNo + 1, num)
}


}