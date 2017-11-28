// there is no element v in A over range low..high
function not_exists (v: int, a: [int]int, low: int, high: int) returns(bool)
{ ( forall j: int :: low <= j  && j <= high  ==>  a[j] != v ) }
				
				
procedure seq_search (a: [int]int, n: int, v: int) returns(found: bool, p: int)
	requires n >= 0;
	ensures found  ==> a[p] == v;
	ensures found ==> 1 <= p && p <= n;
	ensures !found ==> not_exists(v, a, 1, n);
{
	var i: int;
	
	i := 1;  found := false;
	while ( i <= n  &&  !found )
  invariant (1 <= i && i <= n + 1);
	invariant ( found  ==>  a[p] == v );
	invariant (found ==> 1 <= p && p <= n);
	invariant ( !found ==>  not_exists(v, a, 1, i-1) );
	{
		if (a[i] == v)
		{
			p := i;
			found := true;
		}
		else
		{
			i := i + 1;
		}
	}
}
