import data.set
import data.nat.sqrt

open set

namespace relation_2102_ns

/-
We're now going to formally explain
what a "section" is for in Lean. A 
section allows you to specify in one
place a set of parameters that are then
assumed to be arguments to every other
definition in the section.  Here's a
very short little section to illustrate
the concept. Don't proceed until you
understand why the #check is reporting
the type of yo to be (ℕ → ℕ) → ℕ → ℕ,
even though it (looks like) it is
defined as yo (n : ℕ) := f n, with 
just one argument.
-/

section demo
variable f : ℕ → ℕ 
def yo (n : ℕ) := f n
#check yo
end demo

/-
The use of sections can make for
cleaner code, because you don't have
to repeat variable declarations in
each object you define within a
section. But if you don't understand
that every variable in a section is
an implicit parameter to every other
definition in the section, then you
will be mystified when it comes to
understanding those definitions. 
-/

/-
Now we turn to the main content of
this unit: the theory of relations.
-/
section relation_2102_sec
/-
Here we use a section to define two
arguments that are assumed to be present
in each definition in the rest of this 
file. 

First, we let β be any type.
-/
variable {β : Type} 

/-
Here's the key to this unit. We let
r represent a binary relation on values
of type β. Whereas we represent a set
of values of type β, or a property of
such values, as a predicate of type,
β → Prop, we represent in a binary
relation, or a set of pairs, of values
of type, β, as a predicate of type,
β → β → Prop. 
-/
variable (r : β → β → Prop)

/-
So now, when you look at the definitions 
in the rest of this file, you understand 
that each one of them has two additional 
arguments, namely β and r. 
-/


/-
Applying r to two values, x and y, of
type, β, yields a proposition. You can
thus think of r as a property of pairs 
of values. If the proposition is true,
then the ordered pair, (x, y), is in 
the relation, otherwise it's not.
-/
variables x y : β  
#check r x y 

/-
In the preceding example, we wrote 
the relation name before the arguments.
It's often more natural to write in in
between the arguments. We call such a
notation an infix notation. Lean gives
us a way to extend the syntax of Lean
by adding infix operators to reduce to
known prefix operators. Here we define
two infix versions of r, one called R,
and one called ≺. The number, 50, in the
following lines defines the precedence
of this operator, i.e., how tightly it
binds when appearing in an expression
with other operators.
-/

local infix `R`:50 := r
local infix `≺`:50 := r

/-
Now we can use either x R y or x ≺ y
to mean the same thing as r x y. We'll
use the x R y style in the file. Lean's
libraries happen to use x ≺ y, but they
mean the same thing, as we just said.
-/
#check x R y 
#check x ≺ y


-- EXAMPLE: THE EQUALITY RELATION

/-
Let's look at equality as a binary
relation. The first thing to know is
that an expression, such as 1 = 1, is
a convenient way of writing "eq 1 1".
The = notation is defined as an infix
version of eq in just the same way 
that we defined R and ≺ to be infix
versions of r. Check to see that the
following expressions mean the same
thing.
-/
#reduce 1 = 1
#reduce eq 1 1

/-
Let's look at the actual definition
of eq in Lean's libraries. 
-/
#print eq
/-
Just look at the first line, skipping 
the constructor for now. What is says
is that for any Type, α, eq is a binary
relation on values of that type. The "Pi" 
symbol, Π,  is like ∀. ∀ is used when 
working with propositions, but equality 
is defined for any type, so we use Π 
instead. You should read the definition as
saying that if you give eq any type, you 
get back a binary relation on values of 
that type: namely one for which the only 
proofs that can be constructed are given
by eq.refl, which takes just one argument,
α, and returns a proof of α = α.

We thus expect the type of "eq ℕ" to be 
a binary relation on ℕ values. We preface 
eq in the following examples with @, which
tells Lean not to use implicit typing for 
the type argument, α, to eq. We really do 
have to give a type argument explicitly.
-/

#check @eq nat 
#check @eq β 

/-
We now see that for any type, α, such as 
ℕ, or, in this file, β, eq α is a binary 
relation on the set of values of type, α. 
It is thus of type, α → α → Prop. That is
the signal that you're looking at a binary
relation in Lean.
-/

-- REFLEXIVE

/-
A relation is said to be reflexive if
every element in the domain of definition
of the relation (the set on which it is
defined) is related to itself.
-/

def reflexive := ∀ ⦃x⦄, x R x

#check reflexive
#reduce reflexive

#check reflexive (@eq β)
#reduce reflexive (@eq β)

/-
We know that eq β is a binary 
relation defined on the set of
values of type, β. Let's assert 
and prove it.
-/

lemma eq_refl : reflexive (@eq β) :=
begin
unfold reflexive,
intro, apply rfl,
end

/-
Let's take just a minute to unpack
the proposition, reflexive (@eq β).
You have to remember that at this
point in the file, we've already
defined β and r as implicit args to
all definitions, including that of
eq_refl.
-/


-- SYMMETRIC

/-
A relation is symmetric if, whenever
two values, and and y, are related, 
y and x are related, in the opposite
order.
-/
def symmetric := ∀ ⦃x y⦄, x R y → y R x


/-
Let's prove that equality is symmetric.
Of course we're cheating a little here
by using a rule already in the libraries
that eq is symmetric: the rule, eq.symm. 
-/
lemma eq_symm : symmetric (@eq β) :=
begin
unfold symmetric,
intros, 
apply eq.symm, 
assumption,
end


/-
EXERCISE: Is the real-world "likes" 
relation, as in "has-a-crush-on", a  symmetric relation? How about Facebook's 
"likes" relation?
-/

-- TRANSITIVE

/-
A binary relation on values of some 
type, β, is said to be transitive if
whenever x and y are related, and y 
and z are related, then x and z are
related. 
-/
def transitive := 
    ∀ ⦃x y z⦄, x R y → y R z → x R z

/-
EXERCISE: Is equality transitive?
-/

lemma eq_trans : transitive (@eq β) :=
begin
unfold transitive,
intros x y z xy yz,
apply eq.trans xy yz,
end

/-
An equivalence relation is a binary
relation that is reflexive, symmetric,
and transitive.
-/
def equivalence := reflexive r ∧ symmetric r ∧ transitive r

/-
Is eq an equivalence relation? Sure.
-/

theorem eq_equiv : equivalence (@eq β) :=
begin
unfold equivalence,
split, exact eq_refl,
split, exact eq_symm, exact eq_trans,
end

/-
Let's discuss another equivalence 
relation. Consider the set ℕ / 12,
the natural numbers modulo 12. 

What is 2 mod 12? What is 14 mod 12?
What is 26 mod 12. All these numbers,
and indeed any natural number of the
form, 2 + k * 12 are congruent to 2
mod 12. 
-/

#reduce 2 % 12
#reduce 14 % 12
#reduce 26 % 12

/-
This entire set of numbers mod 12 
forms an equivalence class. Let's
formalize and prove this proposition.
-/


/-
First, the relation itself.
-/
def mod_12_equiv : ℕ → ℕ → Prop :=
    λ x y, x % 12 = y % 12

/-
Now a simple test case as a sanity
check.
-/
example : mod_12_equiv 2 14 :=
begin
unfold mod_12_equiv, apply rfl,
end

/-
Let's prove that the whole infinite
set of values of the form n + k * 12
is congruent.
-/
example : 
    ∀ k : ℕ, ∀ n : ℕ, 
    mod_12_equiv n (n + k * 12) :=
begin
intros,
unfold mod_12_equiv,
-- The simp tactic uses many rules to simplify expressions,
-- and can prove them true when trivial would do so
simp,
end

/-
Let's show that mod_12_equiv is an equivalence
-/

example : reflexive mod_12_equiv :=
begin
unfold mod_12_equiv,
unfold reflexive, -- EX: why just x here?
intro, apply rfl,
end

example : symmetric mod_12_equiv :=
begin
unfold symmetric,
intros x y,
unfold mod_12_equiv,
intro h,
-- New tactic: rewrite using an equality
rw h,
end

example : transitive mod_12_equiv :=
begin
unfold transitive,
intros x y z xy yz,
unfold mod_12_equiv at xy,
unfold mod_12_equiv at yz,
unfold mod_12_equiv,
rw xy, assumption,
end 

/- ****** END OF PART I. -/


/-
In the rest of this file, we transition
from x R y notation to x ≺ y. You will 
find both used in mathematical writing.
Be careful not to read x ≺ y as saying
that x is less than y. The ≺ symbol in
this context can refer to any relation
whatsoever.
-/

/-
We now define additional properties of
binary relations on a set. For each of
them, come up with one or more familiar
relations having these, and not having
these, properties.
-/

variable {α : Type} 

def empty_relation := λ a₁ a₂ : α, false

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x 

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

/-
Given a function expressed as a lambda
abstraction, we can easily represent it
as a corresponding relation.
-/

def fun_to_rel : 
  (β → β) → (β → β → Prop) :=
    λ f, 
      λ m n, 
        n = f m

/-
Let's look at the square function as
an example. We've seen it many times.
-/

def square (n :ℕ) := n * n

/-
We can represent it as a relation.
-/

def square_rel := fun_to_rel square

/-
Viewed as a relation, square, and indeed 
any function has a crucial property: that 
of being single-valued. Given any argument,
there is at most one result. Another way to
say this is that if both x R y and x R z,
then it must be that y = z (otherwise there
would be two results for the argument x).
-/

def single_valued := 
  ∀ x y z, (x ≺ y) → (x ≺ z) → (y = z)


-- The square relation is single valued
lemma sv_square_rel : 
  single_valued square_rel :=
begin
  unfold single_valued, 
  unfold square_rel,
  unfold fun_to_rel,
  intros x y z,
  assume y z,
  rw y, rw z,
end


/-
Properties of functions.
-/

/-
We now have two ways to represent
functions: as lambda abstractions
and as single-valued relations. 
We can thus formulate properties
of functions using either way of
representing functions. Here we
formulate these properties using
the relational formulation.
-/


/-
Injective.

A function, here formalized as a
single-valued relation, is said to 
be injective if different arguments 
always give different results. We
express this by saying if x R z 
and y R z then x = y,, otherwise
different arguments would yield
the same result. 
-/

def injective_rel := 
  single_valued r → 
    ∀ x y z, x R z → y R z → x = y 

/-
Mathematicians also call such a 
function "one-to-one", as opposed
to being many-to-one. A many-to-one
function returns the same result for
more than one argument value. 

Carefully compare and contrast the
concepts of being single-valued (which
makes a relation into a function) and
being injective (a property of some 
but not all functions).
-/



/-
We will now prove that the square relation
is single-valued, and thus represents a
function, and moreover that it is injective.

We need a few building blocks to complete
this proof, some of which represent basic
proof-building maneuvers whether using a
proof assistant or not. So let's get going.
-/

/-
First, the square function, which we
expressed as a lambda abstraction, is 
single-valued.
-/
lemma sv_square: 
  ∀ x y z : ℕ, 
    y = square x → z = square x → y = z :=
begin
  intros x y z,
  assume y z,
  rw y, rw z,
end

/-
Second, given any values, x and y, and
a function, f, taking such values, it is
clear that if x = y, then f x = f y. We
will sometimes need to apply a function
to both sides of an equation to change
its form on the way to a proof. Proving
this simple theorem will allow to rewrite
equations by applying functions to both
sides.
-/

theorem f_equal : 
  ∀ { α : Type },
  -- with x and y of some type, α 
  ∀ { x y : α }, 
  -- given a function, f
  ∀ f: α → α, 
  -- and an equality, x = y
  x = y → 
  -- derive the equality, f x = f y
  f x = f y :=
begin
intros,
rw a,
end

/-
Third, the function that we're going
to want to apply to both sides of an
equation is the square root function
for natural numbers. The Lean library
provides this function as nat.sqrt.
See the includes at the top of this
file for inclusion of data.nat.sqrt.

The key piece of knowledge is that the 
Lean libraries also have a proof of the 
following: Given a natural number, n, 
one can derive a proof of sqrt(n*n) = n.

sqrt_eq (n : ℕ) : sqrt (n*n) = n.

We now use this fact to prove another
lemma, namely that the square function
is injective. That is, if x * x = y * y
then x = y. 
-/

lemma square_inj : 
  ∀ x y : ℕ, x * x = y * y → x = y :=
begin
intros x y,
assume h,
-- apply nat.sqrt to both sides of h
have sqrt_both_sides := (f_equal nat.sqrt) h,
-- now simplify sqrt (x * x) to x
rw nat.sqrt_eq at sqrt_both_sides,
-- and sqrt (y * y) to y
rw nat.sqrt_eq at sqrt_both_sides,
-- and that does it
assumption,
end


/-
And now we can show that the square
relation, an alternative representation,
is injective.
-/
example : injective_rel square_rel :=
begin
unfold square_rel,
unfold fun_to_rel,
unfold injective_rel,
unfold single_valued,
unfold square,
assume sv,
intros x y z,
assume sqxz sqyz,
rw sqxz at sqyz,
have pf := square_inj x y sqyz,
assumption,
end

def surjective_rel := single_valued r → ∀ y, ∃ x, x R y 

/-
Certainly the identity relation on the
natural numbers is surjective.
-/

theorem id_nat_surj : surjective_rel (fun_to_rel (λ n : ℕ, n)) :=
begin
unfold surjective_rel,
unfold single_valued,
unfold fun_to_rel,
assume fn,
intro y,
apply exists.intro y,
apply rfl,
end

/-
Finally a function is said to be
bijective if it is both injective
and surjective.
-/
def bijective_rel :=  injective_rel r ∧ surjective_rel r

/-
The identity function is bijective.
-/

theorem id_nat_bij : 
  bijective_rel 
    (fun_to_rel (λ n : ℕ, n)) :=
begin
unfold bijective_rel,
unfold injective_rel,
unfold fun_to_rel,
unfold single_valued,
split,
assume fn,
intros x y z,
assume zx zy,
rw <-zx,
rw <-zy,
apply id_nat_surj,
end


/-
A relation is conceptually similar to a 
set of 2-tuples. However, the syntax is 
different.
-/

def mod_12_equiv': set (ℕ × ℕ) :=
  {tuple | tuple.1 % 12 = tuple.2 % 12}

/-
This won't work:
def mod_12_equiv'': set (ℕ × ℕ) :=
  λ x y, x % 12 = y % 12
-/

--#reduce ∃(n m: ℕ), (n, m) ∈ mod_12_equiv'

example: 
  ∀(n m: ℕ), 
    mod_12_equiv n m ↔ (n, m) ∈ mod_12_equiv' 
:=
begin
  assume n m,
  apply iff.intro,

    unfold mod_12_equiv,
    assume pf_mod_12_equiv,
    unfold mod_12_equiv',
    change n % 12 = m % 12,
    assumption,

    unfold mod_12_equiv',
    assume pf_mod_12_equiv',
    unfold mod_12_equiv,
    change n % 12 = m % 12 at pf_mod_12_equiv',
    assumption,

end


/-
Our intuition is that a set of
tuples can be converted into a 
binary relation and vice versa.
Let's see if we can write two
functions to do such conversions.
If we get the functions right,
then we should be able to show
that if you convert one way and
then back, you get right back to
where you started. Proving such
a theorem about our functions 
would be a very powerful test
that we got them right -- without
ever even having to run them!
-/
def set_of_tuples_to_relation: 
  set (β × β) → (β → β → Prop) 
:=
begin
  assume s,
  exact (λ x y, (x, y) ∈ s),
end

def relation_to_set_of_tuples: 
  (β → β → Prop) → set (β × β)
:=
  λ r, { p : β × β | r p.1 p.2 }

example : ∀ s : set (β × β),
  relation_to_set_of_tuples
    (set_of_tuples_to_relation s) 
      = s
:=
begin
intro s,
unfold relation_to_set_of_tuples,
unfold set_of_tuples_to_relation,
/-
Looks complicated, and you could
use set extensionality to take a
next step, but it seems like this
is mostly simplifying expressions,
so let's ask Lean to try to help.
-/
simp,
/-
Nice! But now go back and make
sure you see exactly why it's 
true. An English language proof
might say something like this.
The set of the left is just the
set of pairs of elements that are
in s, and that's just s, so the
equality holds, and we are done.
-/
end

/-
Let us define a relation R as R1
For example imagine the relation 
“is one or two less than” as 
defined over the naturals. It 
contains the 2-tuples {(0, 1), 
(0, 2), (1, 2), (1, 3), (2, 3), 
(2, 4), (3, 4), (3, 5), etc.}

Now let us define R2 (or R ◦ R) 
as the relation having left-hand 
elements equal to the left-hand 
elements of the tuples in R1, and 
right-hand elements equal to the
corresponding right-hand elements 
of the right-hand elements in R1
E.g., from above this would be 
“is two, three, or four less than”
It contains the 2-tuples {(0, 2), 
(0, 3), (0, 4), (1, 3), (1, 4), 
(1, 5), etc.)

R3 (or R ◦ R2) is the relation 
having left-hand elements having 
left-hand elements equal to the 
left-hand elements of the tuples 
in R1, and right-hand elements 
equal to the corresponding 
right-hand elements of the 
right-hand elements in R2 E.g., 
from the above this would be 
“is three, four, or five less than”
-/

/-

-/
def successor: 
  (β → β → Prop) → (β → β → Prop) :=
begin
  assume r,
  exact λ (x y: β), ∃(b: β), (r x b) ∧ (r b y)
end

/-
Transitive closure. 
Transitive closure is the union of R and all
of its successor relations

We're not ready for the following formal definition
of the transitive closure of a relation, as we
haven't covered inductive definitions, but we can
introduce the idea informally now.
-/

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

end relation_2102_sec

end relation_2102_ns