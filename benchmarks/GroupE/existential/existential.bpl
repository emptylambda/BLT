procedure modify_at(a: [int]int) returns(b: [int]int)
  ensures (exists k: int :: b[k] == a[1]);
{
  b := a[0 := 7];
}	

procedure modify_hint(a: [int]int) returns(b: [int]int)
  ensures (exists k: int :: b[k] == a[1]);
{
  b := a[0 := 7];
	assert (b[1] == a[1]);
}	

procedure modify_hint2(a: [int]int) returns(b: [int]int)
  ensures (exists k: int :: b[k + 1] == a[1]);
{
  b := a[0 := 7];
	assert (b[1] == a[1]);
}	
