// Nil: empty list
// Cons: non-empty list (Node)
datatype List<A> = Nil | Cons(head: A, tail: List<A>)

datatype Pair<A, B> = Pair(fst: A, snd: B)

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
	ensures length(list) == |listToSeq(list)|;
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
	decreases amount;
	requires 0 <= amount <= length(list);
	ensures length(take(list, amount)) == amount;
	ensures forall i :: 0 <= i < amount ==>
		getElementAtIndex(list, i) == getElementAtIndex(take(list, amount), i);
  ensures listToSeq(list)[..amount] == listToSeq(take(list, amount));
	// 1.) define the body of take
	//     - Need recursion
	// 2.) postconditions
{
	if (amount == 0) then Nil else Cons(list.head, take(list.tail, amount - 1))
}

// function method drop<A>(list: List<A>, amount: int): List<A>
// 	requires 0 <= amount <= length(list);
// 	//                          amount +      length(list) - amount == length(list);
// 	//ensures length(take(list, amount)) + length(drop(list, amount)) == length(list);
// 	ensures length(drop(list, amount)) == length(list) - amount;
// 	ensures listToSeq(list)[amount..] == listToSeq(drop(list, amount));
// {
// 	// TODO: implement me
// 	Nil
// }

// append([], [1, 2, 3]) == [1, 2, 3]
// append([1, 2, 3], []) == [1, 2, 3]
// append([1, 2], [3]) == [1, 2, 3]
// append([1, 2], [3, 4]) == [1, 2, 3, 4]
// Hints:
//  -Empty list appended onto any other list L returns L
//  -Non-empty list appended onto any other list L... recursively call append with the
//   rest of the non-empty list
//  -You only need one if
function method append<A>(l1: List<A>, l2: List<A>): List<A>
{
	// if in the else: l1: Cons(...)
	// l2: ???
	// append([1, 2], [3, 4]) == Cons(1, append([2], [3, 4]));
	if (l1.Nil?) then l2 else Cons(l1.head, append(l1.tail, l2))
}

ghost method test_append() {
	// append([1, 2], [3, 4]) == [1, 2, 3, 4]
	assert append(Cons(1, Cons(2, Nil)), Cons(3, Cons(4, Nil))) == Cons(1, Cons(2, Cons(3, Cons(4, Nil))));
}

// zip: is generic in both input lists
//   zip(List<Int>, List<String>) = List<(Int, String)>
// zip: both inputs must be the same length
// zip: output list should be the same length as the input lists

// proven:
//   -Selection sort
//   -Merge sort
//   -Quicksort

// []
// [12]

// [1, 2, 3, ...]
// 1 <= 2
// is_sorted([2, 3, ...])
predicate is_sorted(list: List<int>)
{
	(list.Nil? ==> true) &&
  (list.Cons? && list.tail.Nil? ==> true) &&
	(list.Cons? && list.tail.Cons? ==> list.head <= list.tail.head	&& is_sorted(list.tail))
}

ghost method test_is_sorted() {
	assert is_sorted(Nil); // []
	assert is_sorted(Cons(1, Nil)); // [1]
	assert is_sorted(Cons(1, Cons(2, Nil))); // [1, 2]
	assert is_sorted(Cons(1, Cons(2, Cons(3, Nil)))); // [1, 2, 3]
}

function method list_as_multiset<A>(list: List<A>): multiset<A>
{
	if (list.Nil?) then multiset{} else
		list_as_multiset(list.tail) + multiset{list.head}
}

// merge([], [1, 2, 3]) = [1, 2, 3]
// merge([1, 2, 3], []) = [1, 2, 3]
// merge([1, 3, 5], [2, 3]) == Cons(1, merge([3, 5], [2, 3]))
function method merge(l1: List<int>, l2: List<int>): List<int>
	requires is_sorted(l1); // two 1s
	requires is_sorted(l2); // three 1s
	ensures is_sorted(merge(l1, l2)); // five 1s
	ensures list_as_multiset(l1) + list_as_multiset(l2) == list_as_multiset(merge(l1, l2));
	// every element from l1 should be in the result list
	// every element from l2 should be in the result list
{
	if (l1.Nil?) then l2 else
		(if (l2.Nil?) then l1 else
		(if (l1.head <= l2.head) then Cons(l1.head, merge(l1.tail, l2)) else
		                              Cons(l2.head, merge(l1, l2.tail))))
}

// O(nlg(n))
// def merge_sort(list):
//   if length(list) < 2:
//     return list
//   else:
//     (l1, l2) = split_list_in_two(list) // O(lg(n))
//     sortedL1 = merge_sort(l1)
//     sortedL2 = merge_sort(l2)
//     sortedList = merge(sortedL1, sortedL2) // O(n)
//     return sortedList

// splitAt([10, 11, 12, 13], 0) = Pair(Nil, [10, 11, 12, 13])
function method splitAt<A>(list: List<A>, at: int): Pair<List<A>, List<A>>
	//requires length(list) >= 2;
	requires 0 <= at < length(list);
	ensures length(list) == length(splitAt(list, at).fst) + length(splitAt(list, at).snd);
	ensures list == append(splitAt(list, at).fst, splitAt(list, at).snd);
	ensures list_as_multiset(list) == list_as_multiset(append(splitAt(list, at).fst, splitAt(list, at).snd));
	ensures length(splitAt(list, at).fst) == at;
	ensures length(splitAt(list, at).snd) == length(list) - at;
{
	if (at == 0) then Pair(Nil, list) else
		(var rest := splitAt(list.tail, at - 1);
		 Pair(Cons(list.head, rest.fst), rest.snd))
}

function method splitListInTwo<A>(list: List<A>): Pair<List<A>, List<A>>
	requires length(list) > 1;
{
	// 0 / 2: 0
	// 1 / 2: 0
	// 2 / 2: 1
	// 3 / 2: 1
	splitAt(list, length(list) / 2)
}

method mergeSort(list: List<int>) returns (result: List<int>)
	ensures is_sorted(result);
	ensures list_as_multiset(list) == list_as_multiset(result);
{
	if (length(list) < 2) {
		result := list;
	} else {
		var split := splitListInTwo(list);
		var sortedLeft := mergeSort(split.fst);
		var sortedRight := mergeSort(split.snd);
		result := merge(sortedLeft, sortedRight);
	}
}
