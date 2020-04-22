// Nil: empty list
// Cons: non-empty list (Node)
datatype List<A> = Nil | Cons(head: A, tail: List<A>)

// []: Nil
// [1]: Cons(1, Nil)
// [1, 2]: Cons(1, Cons(2, Nil))
// [1, 2, 3]: Cons(1, Cons(2, Cons(3, Nil)))

// Nil: 0
// Cons(_, tail): length(tail) + 1
function method length<A>(list: List<A>): int
	ensures length(list) >= 0;
	ensures has_length(list, length(list));
{
	if (list.Nil?) then 0 else length(list.tail) + 1
}

predicate has_length<A>(list: List<A>, len: int)
{
	(list.Nil? ==> len == 0) &&
  (list.Cons? ==> exists restLen :: has_length(list.tail, restLen) && len == restLen + 1)
}

ghost method length_works_correctly()
{
	var nil: List<int> := Nil;
	assert length(nil) == 0;
	assert length(Cons(0, Nil)) == 1;
	assert length(Cons(0, Cons(1, Nil))) ==  2;
	assert length(Cons(0, Cons(1, Cons(2, Nil)))) == 3;
}

// issues:
//   -index could get negative
//   -index could be too big
//
// getElementAtIndex(Nil, 0)
// getElementAtIndex(Cons(1, Cons(2, Nil)), 5)
//
function method getElementAtIndex<A>(list: List<A>, index: int): A
	requires 0 <= index < length(list);
	ensures is_element_at_index(list, index, getElementAtIndex(list, index));
{
	if (index == 0) then list.head else getElementAtIndex(list.tail, index - 1)
}

predicate is_element_at_index<A>(list: List<A>, index: int, element: A)
	requires 0 <= index < length(list);
{
	(index == 0 ==> list.head == element) &&
  (index > 0 ==> is_element_at_index(list.tail, index - 1, element))
}

ghost method testGetElementAtIndex() {
	assert getElementAtIndex(Cons(1, Nil), 0) == 1;
	assert getElementAtIndex(Cons(2, Cons(1, Nil)), 1) == 1;
	assert getElementAtIndex(Cons(2, Cons(1, Nil)), 0) == 2;
}

function method listToSeq<A>(list: List<A>): seq<A>
{
	if (list.Nil?) then [] else [list.head] + listToSeq(list.tail)
}

// Cons(1, Cons(2, Cons(3, Nil))): [1, 2, 3]
// take([1, 2, 3], 0) == []
// take([1, 2, 3], 1) == [1]
// take([1, 2, 3], 2) == [1, 2]
// take([5, 6, 3], 2) == [5, 6]
// take([5, 6, 2], 3) == [5, 6, 2]
//
// take([2, 1, 3], -1) == <<INVALID>>
// take([9, 3, 4], 5) == <<INVALID>>
//
function method take<A>(list: List<A>, amount: int): List<A>
	requires 0 <= amount <= length(list);
	ensures length(take(list, amount)) == amount;
	ensures forall i :: 0 <= i < amount ==>
		getElementAtIndex(list, i) == getElementAtIndex(take(list, amount), i);
  //ensures listToSeq(list)[..amount - 1] == listToSeq(take(list, amount));
	// 1.) define the body of take
	//     - Need recursion
	// 2.) postconditions
{
	if (amount == 0) then Nil else Cons(list.head, take(list.tail, amount - 1))
}
