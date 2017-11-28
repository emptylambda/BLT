type ref;
const nil: ref;
const next: [ref] ref;

function dist(from, to: ref) returns (int);
axiom ( forall from, to: ref :: {dist(from, to)}
 (from == to ==> dist(from, to) == 0) &&
 (from != to ==> dist(from, next[to]) == dist(from, to) + 1) );

procedure length(head: ref) returns (len: int)
  ensures len == dist(head, nil);
{
  var cur: ref;
  cur, len := head, 0;
  while (cur != nil)
    free invariant head != cur;
    invariant len == dist(head, cur);
  {
		cur, len := next[cur], len + 1;
	}
}
