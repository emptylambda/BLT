const a: [int] int;
// const d: int; axiom (d > 0);

// axiom (forall i: int :: {a[i]} {:weight 0}			  // (*a*) is sorted
//        0 <= i ==> a[i] < a[i + 1]);

// with trigger it bombs
axiom (forall i: int :: {a[i]} // {:weight 0}	
       0 <= i ==> a[i] < a[i + 1]);
// axiom (forall i, j: int :: 0 <= i && i < j ==> a[i] < a[j]);

function hash(int) returns (int);
axiom (forall x, y: int :: {x > y} 
       x > y ==> hash(x) > y);

// procedure dh(x: int) returns (h: int)
//   ensures h > x;
// { h := hash(x + d); }


procedure ah(k: int) returns (h: int)
  requires k >= 0;
  ensures h > a[k];
{ h := hash(a[k + 1]); }



// const a: [int] int;
// const d: int;

// axiom (d > 0);

// // with trigger it bombs
// // axiom (forall j: int :: // {a[j]} {:weight 0}	
// //        0 <= j ==> a[j] < a[j + 1]);

// // with this def it works in Boogie
// // axiom (forall j, k: int :: // {a[j]} {:weight 0}	
// //        0 <= j && j < k ==> a[j] < a[k]);


// function hash(int) returns(int);
// axiom (forall x, y: int :: x > y ==> hash(x) > y);

// procedure hash_array(i: int) returns(h: int)
//   // using pre and commenting out axiom, it works in Boogie!
//   // requires (forall j: int ::
// 	//           0 <= j ==> a[j] < a[j + 1]);
// 	requires 0 <= i;
// 	ensures h > a[i];
// {
//   h := hash(a[i+1]);
// }	


procedure hash_array(k: int) returns(h: int)
  // using pre and commenting out axiom, it works in Boogie!
  // requires (forall i: int ::
	//           0 <= i ==> a[i] < a[i + 1]);
	requires 0 <= k;
	ensures h > a[k];
{
  h := hash(a[k+1]);
}	

// procedure mhash(b: int) returns(h: int)
// //  requires a == 2*b;
// 	ensures h > b;
// {
//   h := hash(b+d);
// }	
