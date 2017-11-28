const a: [int] int;
const d: int;

axiom (d > 0);

axiom (forall j, k: int :: {a[j], a[k]} {:weight 0}
       0 <= j && j < k ==> a[j] < a[k]);

function hash(int) returns(int);
axiom (forall x, y: int :: x > y ==> hash(x) > y);

procedure hash_array(k: int) returns(h: int)
	requires 0 <= k;
	ensures h > a[k];
{
  h := hash(a[k+1]);
}	
