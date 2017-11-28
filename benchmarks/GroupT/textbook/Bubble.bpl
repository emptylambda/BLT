// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Bubble Sort, where the specification says the output is a permutation of
// the input.

// Introduce a constant 'N' and postulate that it is non-negative
const count: int;
axiom 0 <= count;

// Declare a map from integers to integers.  In the procedure below, 'a' will be
// treated as an array of 'count' elements, indexed from 0 to less than 'count'.
var a: [int]int;

// This procedure implements Bubble Sort.  One of the postconditions says that,
// in the final state of the procedure, the array is sorted.  The other
// postconditions say that the final array is a permutation of the initial
// array.  To write that part of the specification, the procedure returns that
// permutation mapping.  That is, out-parameter 'perm' injectively maps the
// numbers [0..count) to [0..count), as stated by the second and third postconditions.
// The final postcondition says that 'perm' describes how the elements in
// 'a' moved:  what is now at index 'i' used to be at index 'perm[i]'.
// Note, the specification says nothing about the elements of 'a' outside the
// range [0..count).  Moreover, Boogie does not prove that the program will terminate.

procedure BubbleSort() returns (perm: [int]int)
  modifies a;
  // array is sorted
  ensures (forall i, j: int :: 0 <= i && i <= j && j < count ==> a[i] <= a[j]);
  // perm is a permutation
  ensures (forall i: int :: 0 <= i && i < count ==> 0 <= perm[i] && perm[i] < count);
  ensures (forall i, j: int :: 0 <= i && i < j && j < count ==> perm[i] != perm[j]);
  // the final array is that permutation of the input array
  // ensures (forall i: int :: 0 <= i && i < count ==> a[i] == old(a)[perm[i]]);
{
  var n, p, tmp: int;

  n := 0;
  while (n < count)
    invariant n <= count;
    invariant (forall i: int :: 0 <= i && i < n ==> perm[i] == i);
  {
    perm[n] := n;
    n := n + 1;
  }

  while (n > 0)
    invariant 0 <= n && n <= count;
    // array is sorted from n onwards
    invariant (forall i, k: int :: n <= i && i < count && 0 <= k && k < i ==> a[k] <= a[i]);
    // perm is a permutation
    invariant (forall i: int :: 0 <= i && i < count ==> 0 <= perm[i] && perm[i] < count);
    invariant (forall i, j: int :: 0 <= i && i < j && j < count ==> perm[i] != perm[j]);
    // the current array is that permutation of the input array
    // invariant (forall i: int :: 0 <= i && i < count ==> a[i] == old(a)[perm[i]]);
  {
    n := n - 1;
    // if (n < 0) {
    //   break;
    // }

    p := 0;
    while (p < n)
      invariant 0 <= p && p <= n;
      // array is sorted from n+1 onwards
      invariant (forall i, k: int :: n+1 <= i && i < count && 0 <= k && k < i ==> a[k] <= a[i]);
      // perm is a permutation
      invariant (forall i: int :: 0 <= i && i < count ==> 0 <= perm[i] && perm[i] < count);
      invariant (forall i, j: int :: 0 <= i && i < j && j < count ==> perm[i] != perm[j]);
      // the current array is that permutation of the input array
      // invariant (forall i: int :: 0 <= i && i < count ==> a[i] == old(a)[perm[i]]);
      // a[p] is at least as large as any of the first p elements
      invariant (forall k: int :: 0 <= k && k < p ==> a[k] <= a[p]);
    {
      if (a[p+1] < a[p]) {
        tmp := a[p];  a[p] := a[p+1];  a[p+1] := tmp;
        tmp := perm[p];  perm[p] := perm[p+1];  perm[p+1] := tmp;
      }

      p := p + 1;
    }
  }
}
