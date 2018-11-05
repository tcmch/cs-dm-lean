import data.set
open set

/-
In Lean, set is a type constructor. It takes
a type, T, as an argument and returns, as a 
result, the type, set T, which  we read as the
type of any set with elements of type, T. The
type of set is thus Type → Type. Lean tells
us that this type constructor can take a type
in any type universe, i.e., Type, Type 1, etc.
We needn't be concerned with that here.
-/

#check set

/-
EXERCISE: Is set a type? Discuss.
-/

#check set nat

/-
The type, set nat, or set T more 
generally, represents a property
of value of type nat (or T): the
property of "being in a given set!"
-/

#reduce set nat

/-
We now define e to be the empty
set of natural numbers. Lean gives
us ordinary set display notation
(using curly braces around a list
of elements) for this purpose.
-/

def e: set nat := { }

/-
The symbol, ∅, is often used
to represent the empty set (of
values of some type).
-/

def e': set nat := ∅ 

/-
We can't just say "e : set := {}"",
because then Lean does not have 
enough context to infer the type
of the elements.
-/

/-
EXERCISE: What is the property of 
natural numbers that characterizes 
the empty set of natural numbers?
-/

#reduce e

/-
Study that carefully. The predicate 
that defines the empty set is, as
we've alreadydiscussed, false(n):
i.e., the function of type ℕ → Prop
that for any value, n : ℕ, returns
the proposition false. No natural
number can makes the (proposition
derived from the) predicate true, 
so no natural number is in the set
that it represents.
-/

/-
We can also represent the empty 
set using set builder notation.
Set builder notation is also called
set comprehension notation.
-/

def e'' : set nat := { n | false }

def ev(n : ℕ):Prop := ∃ m, m + m = n 

def v : set nat := { n | ev n } 
/-
We read the right hand side as
"the set of values, n, for which
the predicate, false, is true."
As there is no value that makes
false true, the set is empty. It
has no elements.
-/

/-
Here's another set of ℕ, containing 
only the number, 1. We call such a
set a singleton set.
-/

def x: set nat := { 1 }

/-
EXERCISE: What property of natural 
numbers defines the property of being 
in this set? Try to come up with the
answer before you look! 
-/

#reduce x

/-
The answer is a little surprising.
The predicate λ n, n = 1, would do
to define this set, but instead Lean
uses λ n, n = 1 ∨ false. The basic
intuition is that, were we to remove
the 1 from this set, we'd be left 
with the empty set, the predicate
for which is that predicate false.
-/

def x' := { n | n = 1 }

#reduce x'

/-
The two notations give rise to
slightly different but equivalent
predicates.
-/

-- SET MEMBERSHIP

/-
By the notation 1 ∈ x we mean the
proposition that "1 is in, or is 
a member of the set, x." This is
simplythe proposition obtained 
by applying the predicate, x, to
the value, 1. The proposition is
literally the value (x 1). Recall 
that function application works 
by substituting the argument (1)
for the parameter (a) in the body 
of the predicate (function).  In
this case, the predicate, x, is
λ (n : ℕ), n = 1. Applying this
predicate/function the value, 1,
reduces to the proposition that:
1 = 1 ∨ false. This proposition,
in turn, is easy to prove, and so,
yes, indeed, 1 is in the set x.
-/

#reduce 1 ∈ x

example : 1 ∈ x :=
-- 1 = 1 ∨ false
begin
apply or.intro_left,
exact rfl,
end

/-
Because the proposition, 1 ∈ x,
is defined to be the disjunction,
(1 = 1 ∨ false), you can ask Lean 
to change the format of the goal 
accordingly. If doing this makes 
it easier for you to see how to 
proceed with the proof, feel free 
to use it. You can cut and paste
the disjunction from the string
that #reduce 3 ∈ u prints out.
-/


example : 1 ∈ x :=
-- 1 = 1
begin
change 1 = 1 ∨ false,
-- now or.intro_left, but with a shortcut
left,
-- and now exact rfl, but with a shortcut
trivial,
end


-- ANOTHER EXAMPLE

/-
Here's two sets with three
elements each.
-/

def y : set nat := { 1, 2, 3 }
def z : set nat := { 2, 3, 4 }

/-
EXERCISE: What is a predicate
that characterizes membership in
the set, y?
-/

#reduce y


/-
EXERCISE: Define the same set, y,
with the name, y', using set builder
notation.
-/

def y' : set nat := { n | 
    n = 1 ∨ n = 2 ∨ n = 3 }

#reduce y 

/-
With these basics in hand, we can 
define, understand, and work with
the full range of set operations.
Set operations are like operations
with numbers but their operands and
results are sets.
-/

-- SET UNION

/-
The union of two sets, y and z, 
which we denote as y ∪ z, is the
combined set of values from y and 
z. 

An element is either in or not in 
a given, but cannot be in a more 
than one time (otherwise you have
what is called a multiset). The 
union of y and z as defined above 
is thus the set { 1, 2, 3, 4 }.
-/

def u := y ∪ z


/-
EXERCISE: What predicate defines 
the set that is the union of y and z?
-/

#reduce u

/-
Answer: It is the predicate that
defines what it means to be in y 
or to be in z. That is, it is the
disjunction of the predicates that
define y and z, respectively. Union
corresponds to "or."
-/

/-
Let's prove that 3 ∈ u. Let's 
start by reminding ourselves of
the predicate that defines u and
of the proposition represented 
by 3 ∈ u.
-/

#reduce u

/-
The set, u, is defined as a
predicate that takes a : ℕ and
returns the proposition that
that a is one of the values
in the set, expressed as a 
somewhat long disjunction. Lean 
selects the variable name, a, 
for purposes of printing out 
the value of u. There is no
special meaning to a; it is 
just an otherwise unbound name.
-/


/-
Now that we know that 3 ∈ u is 
just a proposition involving a
bunch of disjunctions, it's easy
to prove. -/

example : 3 ∈ u :=
begin
/-
Notice again that Lean leaves the 
goal written using set membership
notation. Just bear in mind that
the goal is just the disjunction,
(3 = 3 ∨ 3 = 2 ∨ 3 = 1 ∨ false) ∨ 
3 = 4 ∨ 3 = 3 ∨ 3 = 2 ∨ false.
-/
left,
left,
trivial,
end

/-
Or, if you prefer, make the goal
explicit as a disjunction.
-/
example : 3 ∈ y ∪ z :=
begin
change (3 = 3 ∨ 3 = 2 ∨ 3 = 1 ∨ false) ∨ 3 = 4 ∨ 3 = 3 ∨ 3 = 2 ∨ false,
apply or.inl,
apply or.inl,
trivial,
end

-- SET INTERSECTION

/-
The intersection of two sets, y and
z, which we denote as y ∩ z, is the
set containing those values that are
in y and that are in z. Intersection
thus corresponds to the conjunction
of the predicates defining the two
individual sets.
-/

def w := y ∩ z

#reduce w

example : 2 ∈ y ∩ z :=
-- (a = 3 ∨ a = 2 ∨ a = 1 ∨ false) ∧ (a = 4 ∨ a = 3 ∨ a = 2 ∨ false)
begin
apply and.intro,
right,
left,
trivial,
right,
right,
left,
trivial,
end


-- SET DIFFERENCE

/-
The set difference y - z, also
writen as y \ z, is the set of
values that are in y but not in
z. Think of the subtraction as
saying that from y you take away
z, and the result is what is left
of y.

EXERCISE: What predicate defines
a set difference, y \ z?
-/

#reduce y \ z

example : 1 ∈ y \ z :=
begin
-- apply and.intro,
split,
right,
right,
left,
trivial,
/-
The goal looks funny, but think
about what it means. It is the
predicate, (λ (a : ℕ), a ∉ z),
applied to the value, 1, which
is to say it's the proposition,
1 ∉ z. That in turn is ¬ 1 ∈ z.
And that, in turn, is just the
proposition that 1 ∈ z → false.
So assume 1 ∈ z and show false 
to prove it. What is 1 ∈ z? It's
the proposition that 1 is one of
the elements in the set, written
as a disjunction, so use case
analysis! 
-/
assume pf,
cases pf,
/-
Now we need a proof that 1 ≠ 4. The 
dec_trivial tactic defined in the Lean's
standard library "decides" many purely 
arithmetic propositions. That is, it 
generates either a proof that such a
proposition is true if it's true. It
will also generate a proof that its
negation is true if that is the case. 
The dec_trivial tactic implements a
"decision procedure" for sufficiently
simple propositions involved numbers.
Here we use it to give us a proof of 
1 ≠ 4. We can then use that to get a 
proof of false and use false elim to 
eliminate the current case on grounds 
that it is based on contradictory
assumptions (and thus can't happen).
-/
have h : 1 ≠ 4 := dec_trivial,
/-
The contradiction tactic looks for a
explicit contradiction in the context
and if it finds one, applies false.elim
to finish proving the goal.
-/
contradiction,
cases pf,
have h : 1 ≠ 3 := dec_trivial,
contradiction,
cases pf,
have h : 1 ≠ 2 := dec_trivial,
contradiction,
have f : false := pf,
contradiction,
end

-- SUMMARY SO FAR

/-
A set can be characterized by
a predicate: one that is true
for each member of the set and
false otherwise.

The union of two sets is given
by the disjunction (or) of the 
predicates:
(a ∈ y ∪ z) = (a ∈ y) ∨ (a ∈ z)

The conjunction is defined by 
their conjunction:
(x ∈ y ∩ z) = (x ∈ y ∧ a ∈ z)

Their difference is defined by 
the conjunction of the first and
the negation of the second:
(a ∈ y \ z) = ( a ∈ y) ∧ (¬ a ∈ z)
-/

-- PART II

/-
Now we introduce addition basic 
set theory concepts: subsets,
power sets, product sets, and
a concept of insertion into a 
set.
-/

-- Subset

/-
Subset, denoted ⊂, is a binary 
relation on sets, denoted X ⊂ Y, 
where X and Y are sets, that is 
true iff every element of X is 
also in (an element of) Y. 

So, { 1, 2 } ⊂ { 1, 2, 3 } but
¬ { 1, 2 } ⊂ { 1, 3, 4}. In the
first case, every element of the
set, { 1, 2 }, is also in the set
{ 1, 2, 3 }, so { 1, 2 } is a 
subset of { 1, 2, 3 }, but that
is not the case for { 1, 2 } and
{ 1, 3, 4 }.

Remember that in Lean, "set" is 
not a type but a type constructor,
a.k.a., a polymorphic type. Rather,
for any type, T, set T is a type,
namely the type of sets containing
elements of type T. Even the empty
set always has an element type, so,
for example, the empty set of ℕ is
not the same as the empty set of 
strings.
-/

/-
EXERCISE: List all of the subsets
of each of the following sets of ℕ. 

* ∅ 
* { 1 }
* { 1, 2 }
* { 1, 2, 3 }

EXERCISE: How many subsets are there
f a set containing n elements. Does 
your formula work even for the empty
set, containing 0 elements?
-/


/-
remember:
* def x : set nat := { 1 }
* def y : set nat := { 1, 2, 3 }
* def z : set nat := { 2, 3, 4 }
-/

#check x ⊆ y
#reduce x ⊆ y

example : x ⊆ y := 
begin
change ∀ ⦃a : ℕ⦄, a = 1 ∨ false → a = 3 ∨ a = 2 ∨ a = 1 ∨ false,
assume a,
intro h,
cases h,
right,
right,
left,
assumption,
contradiction,
end


section sets
/-
We temporarily assume, within this
section, that 
-/
variable T : Type
variable x : T
variables A B C : set T

/-
For any type, T, a set T is a T → Prop:
a property of values of type T, namely
the property of being in the given set.
-/
#reduce set T

/-
Membership, written ∈, where x ∈ A is
read as "x is in A" or "x is a member of
A", is the proposition, (A x), i.e., that
x has the property of being in A.
-/
#reduce x ∈ A

/-
The intersection of A and B, written 
A ∩ B, is the property of being in set 
A and being in set B.
-/
#reduce x ∈ A ∩ B


/-
The union of sets, A and B, written 
A ∪ B, is the property of being in set 
A or being in set B.
-/
#reduce x ∈ A ∪ B


/-
The difference of sets, A and B, written 
A \ B, is the property of being in set 
A and not being in set B.
-/
#reduce x ∈ A \ B

/-
The complement a set, A, written in Lean
as -A, is the property of not being in 
the set, A. 
-/
#reduce x ∈ -A


#reduce A ⊆ B


#check ext 

-- set equality
example : A = B :=
begin
apply ext,
intro x,
apply iff.intro,
intro,
-- etc.
end


/-
A is a subset of A ∪ B
-/
example : ∀ T : Type, ∀ s t: set T, s ⊆ s ∪ t :=
begin
assume T s t x, 
assume h : x ∈ s,
show x ∈ s ∪ t, 
change s x ∨ t x,
change s x at h,
from or.inl h
end

/-
The empty set, ∅, is a subset of any set.
-/
example : ∀ T : Type, ∀ s: set T, ∅ ⊆ s :=
begin
assume T s x,
assume h : x ∈ (∅ : set T),
have f: false := h,
contradiction,
end

/-
Subset is a transitive relation on sets
-/
example : 
    ∀ T : Type, ∀ A B C: set T, 
        A ⊆ B → B ⊆ C → A ⊆ C 
:=
begin
    assume T s t u,
    assume st tu,
    intro,
    intro,
    have z := st a_1,
    exact (tu z),
end  

/-
If an object is in both sets A and B
then it is in their intersection.
-/
example : 
∀ T : Type, forall A B : set T, 
∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B :=
begin
assume T A B x,
assume hA : x ∈ A,
assume hB : x ∈ B,
show x ∈ A ∧ x ∈ B, from
and.intro hA hB,
end


/-
If an object is in some set A or
set B then it is in their union.
-/
example : 
∀ T : Type, forall A B : set T, 
∀ x, x ∈ A ∨ x ∈ B → x ∈ A ∪ B :=
begin
assume T A B x,
intro dis,
show x ∈ A ∨ x ∈ B,
by assumption,
end

-- from Avigad
/-
A minus B is a subset of A
-/
example : A \ B ⊆ A :=
begin
assume x,
assume mem : x ∈ A \ B,
cases mem, 
from mem_left,
end

-- from Avigad
/-
A minus B is contained in the complement of B
-/
example : A \ B ⊆ -B :=
begin
assume x,
assume mem : x ∈ A \ B,
change x ∈ A ∧ ¬ x ∈ B at mem,
change x ∉ B,
exact mem.right,
end

example : A \ B = A ∩ -B :=
begin
apply ext,
intro,
split,
intro h,
exact h,
intro h,
exact h,
end


-- Powerset

/-
The powerset of a set, A, is the set of all
of the subsets of A.
-/

#check powerset A
#check 𝒫 A
#reduce 𝒫 A

/-
Note about implicit arguments. In the preceding
definition we see {{ }} brackets, rendered using
the characters, ⦃ ⦄. This states that the argument
is to be inferred from context (is implicit) but
is expected only when it appears before another
implicit argument. This notation tells Lean not
to "eagerly" consume the argument, as soon as it
can, but to wait to consume it until it appears,
implicitly, before another implicit argument in a
list of arguments. This is a notational detail 
that it's not worth worry about at the moment. 
-/


-- Tuples
/-
If S and T are types, then S × T, called the 
product type of S and T, is the type of ordered
pairs, (s, t), where s : S and t : T. In Lean 
and in ordinary mathematics, elements of such a
type are represented as ordered pairs of values
enclosed in parenthesis.
-/

#check ℕ × ℕ 
#check (1, 2)
/-
This ordered pair notation in Lean in shorthand 
for the appliation of the constructor, prod.mk,
two two arguments. The constructor takes the 
type arguments implicitly.
-/
#check prod.mk 1 2

-- Product set

/-
The Cartesian product set of two sets, A 
and B, denoted as A × B in everyday math,
is the set of all ordered pairs, (a, b) 
(values of type prod A B), where a ∈ A 
and b ∈ B. In Lean, the set product of 
sets, A and B, is denoted as set.prod A B.
There is no nice infix operator notation
for set products at this time.

Note carefully: there is a distinction
here between product types and product sets.
Product types are types, while product sets
are sets. And sets are not types in Lean.
Rather they're specified as properties.

This is potentially confusing. It is made
more confusing by the fact that Lean has 
a way to convert a set into a special type
called a subset type: the type of elements
in the set, along with proofs of membership.
And if you apply prod to two sets, you'll 
get a subset type!
-/

#check set.prod y z     -- product set type
#reduce set.prod y z    -- product set property
#check prod y z         -- oops, a subset type
#check y × z            -- oops, same thing
#reduce prod y z        -- oops, not what we want


/-
A set product is just a set, which is to
say it's defined by a predicate, s. Such a
predicate is true for exactly the members
of the set. That is, (s x) is a proposition
that is true iff x ∈ s. The predicate that
defines a product set is a predicate on
ordered pairs. It's basically defined like
this:
-/

def mysetprod (S T : Type) (s : set S) (t : set T) : set (S × T) :=
{p : prod S T | p.1 ∈ s ∧ p.2 ∈ t}

/-
What this says, then, is that the product set
of s (a set of S-type values) and t (a set of
T-type values) is the set of pairs, p, each of
type (prod S T), and each thus an ordered pair,
p = (p.1, p.2), where p.1 ∈ s and p.2 ∈ t.
-/


example : (1, 2) ∈ set.prod y z := 
begin
change (λ (p : ℕ × ℕ),
  (p.fst = 3 ∨ p.fst = 2 ∨ p.fst = 1 ∨ false) ∧ (p.snd = 4 ∨ p.snd = 3 ∨ p.snd = 2 ∨ false)) (1,2),
  split,
  right,right,left,apply rfl,
  right,right,left,apply rfl,
end

/-
Note: { x // A x} is the same as { x | A x}, and
both are shorthands for "subtype (λ x : α, p x)." 
The idea is that the type, {x : α // p x}, denotes 
the collection of elements of α with property p.
-/
example : { x // A x} = { x | A x} := rfl







-- Insertion

/-
We can provide an operation that we can think
of as "inserting" an element into a set, as a
function that takes an element and a set and
returns the set containing that element along
with the elements of the original set. 
-/

def myInsert { T : Type } (a : T) (s : set T) : set T :=
    {b | b = a ∨ b ∈ s}
#reduce myInsert 5 { 1, 2, 3, 4 }

-- The Lean set library provides "insert"
#reduce insert 5 { 1, 2, 3, 4 }

end sets