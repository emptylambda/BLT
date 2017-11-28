// there is one element equal to v in a over range low..high
function exists_one (v: int, a: [int]int, low: int, high: int) returns(bool)
{ ( exists j: int :: low <= j  && j <= high  &&  a[j] == v ) }
				
				
procedure seq_search (a: [int]int, n: int, v: int) returns(found: bool, p: int)
	requires n >= 0;
	ensures exists_one(v, a, 1, n)   ==>  found && a[p] == v;
	ensures !exists_one(v, a, 1, n)  ==>  !found;
{
	var i: int;
	
	i := 1;  found := false;
	while ( i <= n  &&  a[i] != v )
  invariant (1 <= i && i <= n + 1);
	invariant ( exists_one(v, a, 1, i-1)   ==>  found && a[p] == v );
	invariant ( !exists_one(v, a, 1, i-1)  ==>  !found );	
	{
		i := i + 1;
	}
	if ( i <= n )
	{
		p := i;
		found := true;
	}
}

