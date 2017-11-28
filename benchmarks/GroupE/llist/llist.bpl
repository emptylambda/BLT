// 	Example from:  http://www.rise4fun.com/Boogie/5I

type ref;
const nil: ref;

const item: [ref] int;
const next: ([ref] ref); 

const head: ref;

function seg_len (ii: ref, jj: ref) returns (int);
axiom (forall ii: ref, jj: ref :: {seg_len (ii, jj)}
	((ii == jj) ==> seg_len (ii, jj) == 0)
	&&
	((ii != jj) ==> seg_len (ii, jj) == seg_len(next[ii], jj) + 1)
	);

procedure lemma1 (ii1: ref, jj1: ref);
	ensures seg_len(ii1, next[jj1]) == seg_len(ii1, jj1) + 1;
	
function len (ii: ref) returns (int);
axiom (forall ii: ref :: {len(ii)}
	len(ii) == seg_len(ii, nil));

function not_found (ii: ref, n: int) returns (bool);
axiom (forall ii: ref, n: int ::
	((ii == nil || n == 0) ==> (not_found(ii, n)))
	&&
	((ii != nil) ==> (not_found(ii, n) == (item[ii] != 0) && not_found(next[ii], n-1)))
	);
	
function i_th (ii: ref, n: int) returns (int);
axiom (forall ii: ref, n: int :: {i_th(ii, n)}
	(ii != nil) ==>
		((n == 0) ==> (i_th(ii, n) == item[ii]))
		&&
		((n > 0) ==> (i_th(ii, n) == i_th(next[ii], n-1)))
	);
	
procedure lemma2 (ii2: ref, jj2: ref, n2: int);
	ensures (n2 == seg_len(ii2, jj2)) ==> (item[next[jj2]] == i_th(ii2, n2 + 1)); 

procedure search() returns (i: int)
	ensures not_found (head, i);
	ensures (i < len (head)) ==> i_th (head, i) == 0;
{
	var jj: ref;
	i := 0;
	jj := head;

	while (jj != nil && item[jj] != 0) 
		invariant not_found (head, i);
		invariant i == seg_len (head, jj);
		invariant (jj != nil) ==> (item[jj] == i_th (head, i));
	{
		call lemma1(head, jj);
		call lemma2(head, jj, i);
		jj := next[jj];
		i := i + 1;
	}
}
