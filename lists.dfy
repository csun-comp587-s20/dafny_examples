datatype List<A> = Nil | Cons(head: A, tail: List<A>)

// []: Nil
// [1]: Cons(1, Nil)
// [1, 2]: Cons(1, Cons(2, Nil))
// [1, 2, 3]: Cons(1, Cons(2, Cons(3, Nil)))

// Nil: 0
// Cons(_, tail): length(tail) + 1
function method length<A>(list: List<A>): int
	ensures length(list) >= 0;
{
	if (list.Nil?) then 0 else length(list.tail) + 1
}
