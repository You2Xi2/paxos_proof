type value = nat

datatype vertex = V(id:value)
datatype edge = E(v1:vertex, v2:vertex)

datatype graph = G(vertices:set<vertex>, edges:set<edge>)

predicate isValidGraph(g:graph) {
    && |g.vertices| > 0
    && forall e | e in g.edges :: 
        && e.v1 in g.vertices
        && e.v2 in g.vertices
}

predicate isValidPath(p:seq<edge>) 
    decreases p
{
    if |p| <= 1 then true
    else p[0].v2 == p[1].v1 && isValidPath(p[1..])
}

predicate pathLeadsToTarget(source:vertex, target:value, p:seq<edge>) 
    decreases p
    requires isValidPath(p)
{
    if |p| == 0 then source.id == target
    else 
        var e := p[0];
        pathLeadsToTarget(e.v2, target, p[1..])
}


// Main correct path predicate
predicate isCorrectPath(g:graph, source:vertex, target:value, p:seq<edge>) 
    requires isValidGraph(g)
{
    && (forall e | e in p :: e in g.edges)
    && isValidPath(p)
    && pathLeadsToTarget(source, target, p)
}


method neighborsSeq(edges:set<edge>, n:vertex) returns (nbrs:seq<vertex>) 
    decreases edges;
{
    if |edges| == 0 {
        return [];
    } else {
        var e :| e in edges;
            var nbrs := neighborsSeq(edges-{e}, n);
        if e.v1 == n {
            return [e.v2] + nbrs;
        } else {
            return nbrs;
        }
    }
}


method hasPathBfsImp(g:graph, source:vertex, target:value) returns (b:bool)
    requires isValidGraph(g);
    ensures (exists p :: isCorrectPath(g, source, target, p)) <==> b
{
    var visited := {source};
    var q := [source];
    ghost var processed := {};
    while |q| > 0 
        invariant forall i | 0 <= i < |q| :: q[i] !in processed
        invariant forall v | v in g.vertices :: v in processed ==> v in visited
        decreases g.vertices - processed
    {
        var curr := q[0];
        assert curr !in processed;
        assert |processed + {curr}| > |processed|;
        processed := processed + {curr};
        q := q[1..];
        if curr.id == target {
            b := true;
            return;
        } else {
            var nbrs := neighborsSeq(g.edges, curr);
            var i := 0;
            while i < |nbrs| 
                decreases |nbrs| - i
                invariant forall k | 0 <= k < |q| :: q[k] !in processed
            {
                var n := nbrs[i];
                if n !in visited {
                    visited := visited + {n};
                    assert n !in processed;
                    q := q + [n];
                }
                i := i + 1;
            }
        }
    }
    b := false;
}


/*****************************************************************************************
*                                         Proof Code                                     *
*****************************************************************************************/


// function reachable(g:graph, source:vertex) : set<vertex> 
// {
    
// }
