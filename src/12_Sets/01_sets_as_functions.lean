

/-
What are sets?

In many programming languages, sets are unordered
containers of unique items
{3, 1, 2} and {1, 2, 3} are the same set
{1, 1, 2, 3} is not a set

In Lean, to create a set, you need to first specify
what type is contained in the set (in Lean, a set
cannot contain elements of different types)

A set of naturals (set ℕ) is a map from the naturals
to a proposition. The proposition is whether a natural
number is an element of the set
-/

/-
What are functions?

Functions take one or more inputs and provide one or
more outputs. Technically, functions can take zero inputs
(constant functions), and in some contexts, functions can
have no outputs. Multiple outputs can be combined together
as a single output that is a tuple.

Functions have domains (valid input values) and ranges
(valid output values) and map values in the domain into
values in the range

In Lean, a function that takes inputs of type α and β and
returns an outputs of type γ and δ would have the type:
α → β → γ × δ
-/

namespace function_example

  variables α β γ δ: Type

  variable my_fn: α → β → γ × δ

end function_example

/-
Exercise

What is the domain for your basic (i.e., one that does
not produce imaginary numbers) square root function?

What is the domain for your basic division function?
-/

/-
What are predicates?

Predicates are functions that return a proposition
  E.g., α → β → Prop

Alternatively, predicates are propositions with parameters
  E.g., fromCharlottesville(p: Person): Prop := …
  E.g., onSegment(s: Segment)(p: Point): Prop := …

Note that in Lean, predicates have a return type of
Prop and not bool. In other languages (e.g., PVS), this 
distinction is not meaningful.
-/

/-
How sets can represent predicates

There are two ways that sets can represent predicates

1. The set could have the same domain as the predicate.
Membership in the set would indicate a true proposition.
Non-membership in the set represents a false proposition.

2. The set could follow the same convention as for other
functions… (discussed below)
-/

namespace predicate_set_example

  variables α β: Type

  -- Predicate my_pred
  variable my_pred(a: α)(b: β): Prop

  -- Set my_set
  def my_set: set (α × β) := 
    {tuple | my_pred tuple.1 tuple.2}

end predicate_set_example

/-
How sets can represent functions

Consider a function taking a single natural number that is
only valid over the inputs 1, 2, and 3 (its domain) and
that returns a value that is one greater than its input
(so its range is 2, 3, and 4)

We can represent this as this set of tuples: 
  {(1, 2), (2, 3), (3, 4)}
-/

/-
Exercise

Represent the following functions as sets:
-/

namespace function_set_exercise

  def fn1(n: ℕ) := n + 1

  def fn2(n: ℕ)(m: ℕ) :=
    n / m

  #reduce 2 / 0

  #reduce fn2 2 0

  def fn3(n: ℕ)(m: {a: ℕ // a ≠ 0}) :=
    n / m

--  #reduce fn3 2 0

  variables n d : ℕ

--  #check fn3 n d

end function_set_exercise

/-
Solution
-/

namespace function_set_solution

  def fn1(n: ℕ) := n + 1

  def fn2(n: ℕ)(m: ℕ) :=
    n / m

  def fn3(n: ℕ)(m: {a: ℕ // a ≠ 0}) :=
    n / m

  def set1: set (ℕ × ℕ) :=
    {tuple | tuple.2 = tuple.1 + 1}

  def set1': set (ℕ × ℕ) :=
    {tuple | tuple.2 = fn1 tuple.1}

  example: set1 = set1' := rfl

  def my_tuple := (1, 2, 3)
  #check my_tuple
  #reduce my_tuple.2

  def my_tuple' := ((1, 2), 3)
  #check my_tuple'
  #reduce my_tuple'.1
  #reduce my_tuple'.2

  def set2: set (ℕ × ℕ × ℕ) :=
    {tuple | tuple.2.2 = tuple.1 / tuple.2.1}

  def set3: set (ℕ × {a: ℕ // a ≠ 0} × ℕ) :=
    {tuple | tuple.2.2 = tuple.1 / tuple.2.1}    

end function_set_solution

/-
Exercise

Represent the following functions as a set
-/

namespace function_set_exercise2

  variable fn1: ℕ → ℕ

  variable fn2: ℕ → ℕ → ℕ

  variable fn3: ℕ → ℕ → (ℕ × ℕ)

end function_set_exercise2

/-
Solution
-/

namespace function_set_solution2

  variable fn1: ℕ → ℕ

  def set1: set (ℕ × ℕ) :=
    {tuple | tuple.2 = fn1 tuple.1}

  variable fn2: ℕ → ℕ → ℕ

  def set2: set (ℕ × ℕ × ℕ) :=
    {tuple | tuple.2.2 = fn2 tuple.1 tuple.2.1}

  variable fn3: ℕ → ℕ → (ℕ × ℕ)

  def set3: set (ℕ × ℕ × (ℕ × ℕ)) :=
    {tuple | (tuple.2.2.1, tuple.2.2.2) = 
                 fn3 tuple.1 tuple.2.1}

  def set3': set (ℕ × ℕ × ℕ × ℕ) :=
    {tuple | (tuple.2.2.1, tuple.2.2.2) = 
                 fn3 tuple.1 tuple.2.1}

  example: set3 = set3' := rfl

  def tuple3 := (1, 2, 3, 4)
  #reduce tuple3.1
  #reduce tuple3.2
  #reduce tuple3.2.1
  #reduce tuple3.2.2
  #reduce tuple3.2.2.1
  #reduce tuple3.2.2.2

end function_set_solution2