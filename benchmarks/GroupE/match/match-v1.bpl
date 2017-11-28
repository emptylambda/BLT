type person; 
type db;
const members_db : db;
function isMemb(person) returns(bool);
function match(db, person) returns(person);
function isHappy(person) returns(bool);
function isSatisfied(person) returns(bool);

procedure find_match()
{
   assume(forall p : person :: {isMemb(match(members_db, p))}	
	   isMemb(p) ==> isMemb(match(members_db, p)));

   assume(forall p : person :: {isMemb(p)}							 
	  isMemb(p) ==> isHappy(p));

	 assume(forall p : person ::  {isMemb(match(members_db, p))}	
	  isHappy(match(members_db, p)) ==> isSatisfied(p));

	 assert(forall p: person :: {sk_hack(isMemb(match(members_db, p)))}	 
	  isMemb(p) ==> isSatisfied(p));
}				

function sk_hack(bool) returns(bool);
