// 0: Zero
// 1: Succ(Zero)
// 2: Succ(Succ(Zero))
// 3: Succ(Succ(Succ(Zero)))
datatype Nat = Zero | Succ(n: Nat)

function method add(n1: Nat, n2: Nat): Nat
{
	// 0 + n2 = n2
	// (n1 + 1) + n2 = 1 + (n1 + n2)
	if (n1.Zero?) then n2 else Succ(add(n1.n, n2))
}

lemma add_is_commutative(n1: Nat, n2: Nat)
	ensures add(n1, n2) == add(n2, n1);
{
	if (n1.Zero?) {
		assert add(n1, n2) == add(n2, n1);
	} else {
		add_is_commutative(n1.n, n2);
		assert add(n1, n2) == add(n2, n1);
	}
}

lemma add_is_associative(n1: Nat, n2: Nat, n3: Nat)
	ensures add(add(n1, n2), n3) == add(n1, add(n2, n3));
{}

function method lessThan(n1: Nat, n2: Nat): bool
{
	// 0 < (n + 1)
	// (n1 + 1) < (n2 + 1) if n1 < n2
	if (n1.Zero? && n2.Succ?) then true else
	  (if (n1.Succ? && n2.Succ?) then lessThan(n1.n, n2.n) else false)
}

lemma lessThan_is_transitive(n1: Nat, n2: Nat, n3: Nat)
	ensures lessThan(n1, n2) && lessThan(n2, n3) ==> lessThan(n1, n3);
{
	if (n1.Zero? || n2.Zero? || n3.Zero?) {
		assert lessThan(n1, n2) && lessThan(n2, n3) ==> lessThan(n1, n3);
	} else {
		lessThan_is_transitive(n1.n, n2.n, n3.n);
		assert lessThan(n1, n2) && lessThan(n2, n3) ==> lessThan(n1, n3);
	}
}

// equals
// equals(0, 0): true
// equals(n1 + 1, n2 + 1): equals(n1, n2)
// equals(_, _): false
function method equals1(n1: Nat, n2: Nat): bool
{
	if (n1.Zero? && n2.Zero?) then true else
		(if (n1.Zero? || n2.Zero?) then false else equals1(n1.n, n2.n))
}

function method equals2(n1: Nat, n2: Nat): bool
{
	if (n1.Zero? && n2.Zero?) then true else
		(if (n1.Succ? && n2.Succ?) then equals2(n1.n, n2.n) else false)
}

lemma equals1_is_equivalent_to_equals2(n1: Nat, n2: Nat)
	ensures equals1(n1, n2) == equals2(n1, n2);
{
}

lemma equals_is_transitive_with_dafny_equals(n1: Nat, n2: Nat, n3: Nat)
	ensures n1 == n2 && n2 == n3 ==> n1 == n3;
{}

lemma equals_is_transitive_with_own_equals(n1: Nat, n2: Nat, n3: Nat)
	ensures equals1(n1, n2) && equals1(n2, n3) ==> equals1(n1, n3);
{
	if (n1.Zero? || n2.Zero? || n3.Zero?) {
		assert equals1(n1, n2) && equals1(n2, n3) ==> equals1(n1, n3);
	} else {
		equals_is_transitive_with_own_equals(n1.n, n2.n, n3.n);
		assert equals1(n1, n2) && equals1(n2, n3) ==> equals1(n1, n3);
	}

}

// equals(n1, n2) && equals(n2, n3) ==> equals(n1, n3)
