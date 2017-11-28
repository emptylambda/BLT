// Node type
type ref;
const null: ref;
// Node --> Node
type link = [ref] ref;
// Node --> Value
type val = [ref] int;


// Left child
var left: link;
// Right child
var right: link;
// Parent
var parent: link;
// Values
var value: val;
// Root
var root: ref;


// binary tree invariant
function is_tree(l, r, p: link, v: val) returns(bool);
axiom (forall l, r, p: link, v: val, n: ref :: is_tree(l, r, p, v) && n != null && p[n] != null  ==>  n == r[p[n]] || n == l[p[n]] );
axiom (forall l, r, p: link, v: val, n: ref :: is_tree(l, r, p, v) && n != null && l[n] != null  ==>  p[l[n]] == n );
axiom (forall l, r, p: link, v: val, n: ref :: is_tree(l, r, p, v) && n != null && r[n] != null  ==>  p[r[n]] == n );

// binary search tree is a special kind of binary tree
function is_bst(l, r, p: link, v: val) returns(bool);
axiom (forall l, r, p: link, v: val :: is_bst(l, r, p, v) ==> is_tree(l, r, p, v));
// Invariant property of bst (not actually used)
// axiom (forall l, r, p: link, v: val, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, l[x], y) ==> v[y] <= v[x]);
// axiom (forall l, r, p: link, v: val, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, r[x], y) ==> v[y] >= v[x]);
// Invariance when adding node:
	// To an empty tree
axiom (forall l, r, p: link, v: val, n, x: ref :: is_bst(l, r, p, v) && in(l, r, p, v, n, n) && inode(l, r, p, v, n, v[x]) == n && l[x] == null && r[x] == null && 
															n == null  ==>  is_bst(l, r, p[x := n], v));
	// As left child
axiom (forall l, r, p: link, v: val, n, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, n, y) && inode(l, r, p, v, n, v[x]) == y && l[x] == null && r[x] == null && 
															n != null && v[x] <= v[y]  ==>  is_bst(l[y := x], r, p[x := y], v) && in(l[y := x], r, p[x := y], v, n, x));
	// As right child
axiom (forall l, r, p: link, v: val, n, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, n, y) && inode(l, r, p, v, n, v[x]) == y && l[x] == null && r[x] == null && 
															n != null && v[x] >= v[y]  ==>  is_bst(l, r[y := x], p[x := y], v) && in(l, r[y := x], p[x := y], v, n, x));

// node y is in the tree rooted in x
function in(l, r, p: link, v: val, x, y: ref) returns(bool);
axiom (forall l, r, p: link, v: val, n: ref  ::  is_tree(l, r, p, v) ==> in(l, r, p, v, n, n));
axiom (forall l, r, p: link, v: val, n, x: ref  ::  is_tree(l, r, p, v) && in(l, r, p, v, n, x) ==> in(l, r, p, v, n, l[x]) && in(l, r, p, v, n, r[x]));

// value k is in the tree rooted in n
function has(l, r, p: link, v: val, n: ref, k: int) returns(bool)
{ (exists x: ref :: x != null && in(l, r, p, v, n, x) && v[x] == k) }
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && has(l, r, p, v, n, k) && k < v[n] ==> l[n] != null && has(l, r, p, v, l[n], k));
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && has(l, r, p, v, n, k) && k > v[n] ==> r[n] != null && has(l, r, p, v, r[n], k));
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && has(l, r, p, v, n, k) && l[n] == null ==> k >= v[n]);
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && has(l, r, p, v, n, k) && r[n] == null ==> k <= v[n]);

// leftmost node in the tree rooted in `n'
function leftmost(l, r, p: link, v: val, n: ref) returns(ref);
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && l[n] == null ==> leftmost(l, r, p, v, n) == n);
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && l[n] != null ==> leftmost(l, r, p, v, l[n]) == leftmost(l, r, p, v, n));

// minimum value in the tree rooted in `n'
function min(l, r, p: link, v: val, n: ref) returns(int)
{ v[leftmost(l, r, p, v, n)] }

// lowest ancestor of node `n' whose left child is also an ancestor
function lowest_ancestor_leftchild(l, r, p: link, v: val, n: ref) returns(ref);
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && p[n] == null ==> 
																	lowest_ancestor_leftchild(l, r, p, v, n) == null);
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && p[n] != null && l[p[n]] == n ==> 
																	lowest_ancestor_leftchild(l, r, p, v, n) == p[n]);
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && p[n] != null && r[p[n]] == n ==> 
																	lowest_ancestor_leftchild(l, r, p, v, n) == lowest_ancestor_leftchild(l, r, p, v, p[n]));

// successor node of node `n'
function succ(l, r, p: link, v: val, n: ref) returns(ref);
// the successor of a node with right subtree is the subtree's leftmost node
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && r[p[n]] == n ==> succ(l, r, p, v, p[n]) == leftmost(l, r, p, v, n));
// the successor of a node n with no right subtree is n's lowest ancestor whose left child is also an ancestor
axiom (forall l, r, p: link, v: val, n: ref  ::  is_bst(l, r, p, v) && n != null && r[n] == null ==> succ(l, r, p, v, n) == lowest_ancestor_leftchild(l, r, p, v, n));

// insertion node for a new node with value `k' in tree rooted in `n'
function inode(l, r, p: link, v: val, n: ref, k: int) returns (ref);
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n == null ==> inode(l, r, p, v, n, k) == n);
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && l[n] == null && k <= v[n] ==> inode(l, r, p, v, n, k) == n);
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && r[n] == null && k >= v[n] ==> inode(l, r, p, v, n, k) == n);
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && l[n] != null && k <= v[n] ==> inode(l, r, p, v, n, k) == inode(l, r, p, v, l[n], k));
axiom (forall l, r, p: link, v: val, n: ref, k: int  ::  is_bst(l, r, p, v) && n != null && r[n] != null && k >= v[n] ==> inode(l, r, p, v, n, k) == inode(l, r, p, v, r[n], k));


// Add `node' to the tree
procedure put_bst (node: ref) returns (result: ref)
	requires is_bst(left, right, parent, value);
	requires node != null;
	requires !in(left, right, parent, value, root, node);
	requires parent[root] == null;  // This is an invariant of bst, which we encode as precondition for simplicity
	requires left[node] == null && right[node] == null;
	modifies left, right, parent, root;
	ensures parent[root] == null;
	ensures in(left, right, parent, value, root, node);		// Cannot prove this post if switched with the next one!
	ensures is_bst(left, right, parent, value);
{
	var x, y: ref;
	y := null;
	x := root;
	while (x != null)
		invariant is_bst(left, right, parent, value);
		invariant in(left, right, parent, value, root, x);
		invariant y != null ==> left[y] == x || right[y] == x;
		invariant y != null ==> in(left, right, parent, value, root, y);
		invariant root != null && x == null ==> y != null;
		invariant x == null ==> inode(left, right, parent, value, root, value[node]) == y;
		invariant x != null ==> inode(left, right, parent, value, root, value[node]) == inode(left, right, parent, value, x, value[node]);
	{
		y := x;
		if (value[node] < value[x]) {
			x := left[x];
		} else {
			x := right[x];
		}
	}
	parent[node] := y;
	if (y == null) {
		root := node;
	} else {
		if (value[node] < value[y]) {
			left[y] := node;
		} else {
			right[y] := node;
		}
	}
}


// Node with the successor value in the tree
procedure successor_bst (node: ref) returns (result: ref)
	requires is_bst(left, right, parent, value);
	requires node != null;
	ensures result == succ(left, right, parent, value, node);
{
	var x, y: ref;
	x := node;
	if ( right[x] != null ) {
		call result := minimum_bst (right[x]);
	} else {
		y := parent[x];
		while ( y != null && x == right[y] )
			invariant is_bst(left, right, parent, value);
			invariant y == parent[x];  // not necessary for the proof
			invariant x != null;
			invariant lowest_ancestor_leftchild(left, right, parent, value, x) == lowest_ancestor_leftchild(left, right, parent, value, node);
		{
			x := y;
			y := parent[y];
		}
		result := y;
	}
}


// Node with the minimum value in the tree rooted in `node'
procedure minimum_bst (node: ref) returns (result: ref)
	requires is_bst(left, right, parent, value);
	requires node != null;
	ensures result == leftmost(left, right, parent, value, node);
	ensures min(left, right, parent, value, node) == value[result];
{
	var x: ref;
	x := node;
	while ( left[x] != null )
		invariant is_bst(left, right, parent, value);
		invariant in(left, right, parent, value, node, x);
		invariant x != null;
		invariant leftmost(left, right, parent, value, x) == leftmost(left, right, parent, value, node);
	{
		x := left[x];
	}
	result := x;
}


 // Node with value `key' if one exists, otherwise null
 procedure has_bst (key: int) returns (result: ref)
	requires is_bst(left, right, parent, value);
	requires root != null;
	ensures has(left, right, parent, value, root, key) ==> in(left, right, parent, value, root, result) && value[result] == key;
	ensures !has(left, right, parent, value, root, key) ==> result == null;
{
	result := root;
	while ( result != null && value[result] != key ) 
		invariant is_bst(left, right, parent, value);
		invariant result != null ==> in(left, right, parent, value, root, result);
		invariant has(left, right, parent, value, root, key) ==> result != null && has(left, right, parent, value, result, key);
	{
		if ( key < value[result] ) {
			result := left[result];
		} else {
			result := right[result];
		}
	}
}
