lemma addition_is_commutative(n1: int, n2: int)
	ensures n1 + n2 == n2 + n1;
{}

lemma addition_is_associative(n1: int, n2: int, n3: int)
	ensures n1 + (n2 + n3) == (n1 + n2) + n3;
{}

lemma equality_is_transitive(n1: int, n2: int, n3: int)
	ensures (n1 == n2 && n2 == n3) ==> n1 == n3;
{}

lemma addition_always_adds(x: int)
	ensures x < x + 1;
{}

lemma less_than_is_transitive(n1: int, n2: int, n3: int)
	ensures (n1 < n2 && n2 < n3) ==> n1 < n3;
{}

lemma less_than_implies_nonequality(n1: int, n2: int)
	ensures n1 < n2 ==> n1 != n2;
{}

lemma less_than_is_not_greater_than(n1: int, n2: int)
	ensures n1 < n2 ==> !(n1 >= n2);
	ensures (n1 < n2) != (n1 >= n2);
{}

lemma multiplication_is_commutative(n1: int, n2: int)
	ensures n1 * n2 == n2 * n1;
{}

predicate less_than(n1: int, n2: int)
{
	n1 < n2
}

predicate is_sorted1(list: seq<int>)
{
	// [0, 0, 1, 2, 3, 4, 4, 4, 5]
	//  i        j
	//  i  j
	//        i                 j
	//
	// pick one index i
	// pick another index j
	// if i < j then list[i] <= list[j]

	forall i, j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}

predicate is_sorted2(list: seq<int>)
{
	// -empty lists are sorted
  // -lists of length 1 are sorted
	// -for a list of length 2+, it's sorted if the first element is
	//  <= the second element, and the rest of the list is sorted, starting
	//  from the second element
	//
	// [0, 0, 1, 2, 3, 4, 4, 4, 5]
	//  f  s  f <= s
  // [0, 1, 2, 3, 4, 4, 4, 5]
	//  f  s  f <= s
	// [1, 2, 3, 4, 4, 4, 5]
	//  f  s  f <= s
	// ...
	// [5]
	// length 1: sorted

	|list| == 0 ||
	|list| == 1 ||
  (|list| >= 2 && list[0] <= list[1] && is_sorted2(list[1..]))
}

lemma test_sorted()
{
	assert is_sorted1([0, 0, 1, 2, 3, 4, 4, 4, 5]);
	assert is_sorted2([0, 0, 1, 2, 3, 4, 4, 4, 5]);
	assert is_sorted1([0, 0, 0]);
	assert is_sorted2([0, 0, 0]);
	assert is_sorted1([]);
	assert is_sorted2([]);
	is_sorted1_is_equivalent_to_is_sorted2([1, 2, 1]);
	assert !is_sorted1([1, 2, 1]);
	assert !is_sorted2([1, 2, 1]);
	is_sorted1_is_equivalent_to_is_sorted2([3, 1, 2]);
	assert !is_sorted1([3, 1, 2]);

	another_equivalence();
	//assert forall list :: is_sorted1(list) == is_sorted2(list);
	//assert forall list :: is_sorted1_is_equivalent_to_is_sorted2(list);
	assert !is_sorted1([1, 3, 1]);
	assert !is_sorted1([1, 2, 1, 2]);
	assert !is_sorted2([1, 2, 1, 2]);
}

lemma another_equivalence()
	ensures forall list :: is_sorted1(list) == is_sorted2(list);
{}

lemma is_sorted1_is_equivalent_to_is_sorted2(list: seq<int>)
	ensures is_sorted1(list) == is_sorted2(list);
{}

// method binary_search(list: seq<int>)
// 	requires is_sorted1(list);
// {}

// method selection_sort(list: seq<int>)
// 	ensures is_sorted1(list);
// {}
