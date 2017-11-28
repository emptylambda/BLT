const a: [int] int;
const d: int;

axiom (d > 0);

function hash(int) returns(int);
axiom (forall x, y: int :: x > y ==> hash(x) > y);

procedure hash_array(k: int) returns(h: int)
	requires 0 <= k;
	requires (forall i: int :: {a[i]} {:weight 0}	
            0 <= i ==> a[i] < a[i + 1]);
	ensures h > a[k];
{
  h := hash(a[k+1]);
}	
