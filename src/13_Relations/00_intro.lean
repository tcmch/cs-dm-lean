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


/- Closures of relations -/

def reflexive_closure /- of r -/ :=
  λ x y : β, (r x y) ∨ (x = y)

def symmetric_closure /- of r -/ :=
  λ x y : β, (r x y) ∨ (r y x)

/-
We're not yet ready for the following 
formal definition of the transitive 
closure of a relation, as we haven't 
covered inductive definitions, but we 
can introduce the idea informally.
Informally, it says that if there is
any path from x to y in R then (x, y)
is in the transitive closure of R.
-/

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

/-
EXAMPLE: What is the transitive closure
of the successor relation on the natural 
numbers?
-/

/- *** FUNCTIONS AND THEIR PROPERTIES *** -/

/- The property of being single valued -/

/-
We define a critical property of every 
function. Any function is single valued.
Given any argument, there is at most one 
result. Another way to say this is that 
if y = f x and z = f x, then it must be
the case that y = z, for otherwise there
would be two different results possible
for the value of f x.

EXERCISE: Name a familiar operation that
is not a function because it's not single
valued.
-/

def single_valued_fun
  (f : α → β) : Prop :=
    ∀ x : α, ∀ y z : β, 
      y = f x → z = f x → y = z

/-
Let's look at the square function as
an example. We've seen it many times.
-/

def square (n :ℕ) := n * n

/-
We can easily prove that square is
single valued.
-/

lemma square_single_valued_fun : 
  single_valued_fun square :=
begin
unfold single_valued_fun,
intros x y z ysqx zsqx,
rw ysqx, rw zsqx,
end

/-
Indeed, we can prove that any function
in Lean is single valued. And that is 
not surprising, since the distinguishing
feature of a function is that it has this
property!
-/

theorem every_function_single_valued :
  ∀ f : α → β, single_valued_fun f :=
begin
  intro f, 
  unfold single_valued_fun,
  intros x y z,
  assume yfx zfx,
  rw yfx, rw zfx,
end

/- A lambda represents a total function. -/

/-
A function is said to be total if it is
defined, which is to say it has / returns
a value for every argument value in its
domain of definition. 

In Lean, the domain of definition of a 
function is a type. We've already seen
that a function (value) of type α → β 
defines a way to convert any value of
type α into some value of type β. To
"prove" the type α → β we have assume
that we have some arbitary a : α and
we construct and return a value of type
β. Thus any lambda abstraction in Lean
represents a total function: one that 
is defined for every value of type α.  
-/

/- Encoding Functions as Relations -/

/-
Given any function expressed as a lambda
abstraction, we can easily represent it
as a corresponding relation. Here's a one
line converter.
-/

def fun_to_rel (f : (β → β)): (β → β → Prop) :=
  -- the relation is the set of pairs (m, f m)
  λ m n, n = f m


/-
Here we convert square to a relation.
-/

def square_rel := fun_to_rel square

/-
We can't "apply" a relation to an
argument to compute a result. That
is, we can't compute with relations.
-/

-- We can compute with functions
#reduce square 3

-- This doesn't work with relations
#reduce square_rel 3 -- not 9!

/-
But we can use logic prove that given
pairs of values are in a relation.
-/
example : square_rel 3 9 :=
begin
unfold square_rel, 
unfold fun_to_rel,
apply rfl,
end

/-
Why would we want to represent a 
function as a relation? Giving up 
the ability to compute seems like 
(and is) a high cost. What do we 
get for it? What we get for it is 
the ability to represent partial 
functions. A partial function is
a function that is not necessarily 
defined for every value in its 
domain of definition. 
-/

/-
The square function, for example,
is defined for every value of type
ℕ. Suppose we wanted to represent
a partial function that is just
like the square function but that
is defined only for the values, 0,
1, 2, and 3. Here's how we can do 
it.
-/

def square_partial : ℕ → ℕ → Prop :=
  λ m n,
    (m = 0 ∧ n = 0) ∨
    (m = 1 ∧ n = 1) ∨ 
    (m = 2 ∧ n = 4) ∨ 
    (m = 3 ∧ n = 9)

/-
To prove that the square_partial 
relation represents a mathematical 
function, we have to prove that 
it's single valued. To this end,
we give a definition of what it
means for a relation to be single
valued in general. Remember that
this definition assumes that β is
a type, that x, y, and z are of
type β, and that ≺ is just infix
notation for a relation, r : β → β. 
-/

def single_valued_rel := 
  ∀ x y z, (x ≺ y) → (x ≺ z) → (y = z)


/-
Let's assert and prove that our
partial square relation is actually 
a function, i.e., is single valued.
It is a strictly partial function,
i.e., is a partial function and is
not a total function.

Note: some mathematicials consider
the total functions to be a subset
of the the partial functions (which
is what we do here). Others consider
these sets to be disjoint, i.e., that
if a function is partial if and only
if it is not total. We will use the 
term "strictly partial" for that.
-/

lemma sv_square_rel : 
  single_valued_rel square_partial :=
begin
  unfold single_valued_rel, 
  unfold square_partial,
  intros x y z,
  assume h1 h2,

  cases h1 with x0y resty, 
  cases h2 with x0z restz,

  cases x0y,
  cases x0z,
  rw x0y_right,
  rw x0z_right,

  cases x0y,
  cases restz with x1z rest,
  cases x1z,
  -- we can rewrite hypotheses, too!
  rw x0y_left at x1z_left,
  contradiction,

  -- the rest in the same tedious way
  sorry
end

/-
We can even prove that it's strictly
partial by showing that there actually
is a value on which it's not defined.
Such a value is 4.
-/

lemma square_rel_strictly_partial :
  ∃ m : ℕ, ¬ ∃ n : ℕ, square_partial m n :=
begin
apply exists.intro 4,
unfold square_partial,
assume h,
-- We use cases in several ways here
cases h with w rel,
cases rel, cases rel, contradiction,
cases rel, cases rel, cases rel_left,
cases rel, cases rel, cases rel_left,
cases rel, cases rel_left,
end

/-
Properties of functions.
-/

/-
In this section, we introduce 
several more crucial properties 
of functions, beyond the essential 
property of being single valued.
In particular, we introduce the
concepts of injective functions,
surjective functions, and bijective
functions, which are both injective
and surjective.
-/ 

/-
We now have two ways to represent
functions: as lambda abstractions
and as single-valued relations. 
In this section, to define these
properties of functions in a way
that is applicable to both total
and partial functions, we formulate
them using our representation of
functions as single valued relations.
-/

/-
The property of being injective.

A function is said to  be injective 
if different arguments always give 
different results. We express this 
by saying if x R z and y R z then 
x = y; otherwise different arguments 
would yield the same result. 
-/

def injective_rel := 
  single_valued_rel r → 
    ∀ x y z, x R z → y R z → x = y 

/-
Note that we make being single
valued a "pre-condition" for being
injective. The concept of being
injective only applies to relations
that are actually functions. 
-/

/-
Mathematicians also use the phrase
"one-to-one" to mean injective. This 
term is in contrast to a many-to-one
function, which can return the same 
result for multiple argument values. 

EXERCISE: Give examples of familiar
functions that are injective and that
are not injective.

Carefully compare and contrast the
concepts of being single-valued (which
makes a relation into a function) and
being injective (a property of some 
but not all functions).
-/


/-
We will now prove that the square relation
is single-valued thus represents a function
and as such is injective. We need a few 
building blocks to complete this proof. 
-/

/-
First, we already proved that the square 
function, expressed as a lambda abstraction, 
is single-valued.
-/

#check square_single_valued_fun

/-
Second, we can now formalize one of the
key ideas you've seen throughout your
mathematical career: given an equation,
x = y, we can "do the same thing to both
sides" and we will still have an equation.
We formalize this idea by showing that
if we have x = y, we can apply any 
function, f, to each side, and we will
still have an equation. We prove this
as a general principle. The proof is
by trivial rewriting.
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
Now, the function that we're 
going to want to apply to both 
sides of an equation to prove 
that our square relation is an
injective function is the square 
root function for natural numbers. 
The Lean library provides this 
function as nat.sqrt. See the 
includes at the top of this file 
for inclusion of data.nat.sqrt.

To use proof assistants such as
Lean or Coq in practice, at some
point it becomes necessary to 
learn what's in various libraries
of already defined functions and
proved results. 

The key pieces of knowledge you
need for now are that the library
also has a proof of the following: 
For any a natural number, n, there 
is a proof of nat.sqrt (n * n) = n.

sqrt_eq (n : ℕ) : sqrt (n * n) = n.

Here's an example of how we can 
use f_equal and nat.sqrt together.
-/

-- introduce two variables to use
variables s t : ℕ 
-- assume s squared equals t squared
variable s2t2 : s * s = t * t
-- apply square root to both sides
#check (f_equal nat.sqrt) s2t2


/-
With that library knowlege in hand, 
we prove that the square function, 
formalized as a lambda abstraction,
is injective. Thus, if x * x = y * y
then x = y. 
-/

lemma square_injective : 
  ∀ { x y : ℕ }, x * x = y * y → x = y :=
begin
intros x y,
assume h,
-- apply nat.sqrt to both sides of h
have sqrt_both_sides := (f_equal nat.sqrt) h,
-- use sqrt_eq to simplify sqrt (x * x) to x
rw nat.sqrt_eq at sqrt_both_sides,
-- and sqrt (y * y) to y
rw nat.sqrt_eq at sqrt_both_sides,
-- and that does it
assumption,
end


/-
And now we can show that the square
function represented as a relation 
is injective.
-/
example : injective_rel square_rel :=
begin
unfold square_rel,
unfold fun_to_rel,
unfold square,
unfold injective_rel,
assume sv,
unfold single_valued_rel at sv,
intros x y z,
assume sqxz sqyz,
rw sqxz at sqyz,
have pf := square_injective sqyz,
assumption,
end

/-
The property of being surjective.

A function, f : α → β is said to be 
surjective if it "covers" every value 
in its co-domain, β. That is, it is
surjective if for any value of type
β there is some value of type α such
that f α = β. 

We formalize the concept of being a
surjective function for a relational
formulation of functions, so that the
concept applies to partial functions
as well as total functions. We make
being single valued (being a function)
a pre-condition. 
-/

def surjective_rel := 
  single_valued_rel r → ∀ y, ∃ x, x R y 

/-
Exercise: Is the square function on 
natural numbers, taking each natural
number to its square, surjective? How
would you prove that your answers is
correct?
-/

/-
Certainly the identity relation on the
natural numbers, id_nat := λ n : ℕ, n,
is surjective. To prove it, consider 
an arbitrary y : ℕ and show that there
exists and x such that id_nat x = y. 
The witness is just y itself.
-/

def id_nat := (λ n : ℕ, n)

def id_nat_rel := fun_to_rel id_nat

theorem id_nat_surj : 
  surjective_rel (id_nat_rel) :=
begin
unfold surjective_rel,
unfold single_valued_rel,
unfold id_nat_rel,
assume fn,
intro y,
apply exists.intro y,
apply rfl,
end

/-
EXERCISE: Suppose that f is an encryption
function. When applied to a plaintext, t,
it yields a cyphertext, c. To decrypt the
cyphertext, to recover the plaintext, one
applies a decryption function, g, to c. 
Should f injective? What if it weren't?
-/


/-
Finally a function is said to be
bijective if it is both injective
and surjective.
-/
def bijective_rel :=  
  injective_rel r ∧ surjective_rel r

/-
We've already proved that the
identity function is surjective.
-/

/-
We need to prove it's injective.
-/

lemma id_nat_inj : 
  injective_rel id_nat_rel :=
begin
  unfold id_nat_rel,
  unfold fun_to_rel,
  unfold injective_rel,
  unfold id_nat,
  assume h,
  intros x y z,
  assume zidx zidy,
  rw <-zidx,
  rw <-zidy,
end

theorem id_nat_bij : 
  bijective_rel id_nat_rel :=
begin
exact ⟨id_nat_inj, id_nat_surj⟩ 
end

/-
Functions and Relations as Sets of Pairs
-/

/-
We've already seen that we can represent
a total function, f : β → β, as a relation,
of type β → β → Prop, and that while we
give up being able to compute we gain the
ability to represent *partial* functions 
in this form.

What we show show briefly is that we can
also convert back for betwen relations and
sets of pairs. That means we can represent
any function, whether total or not, as a
set of pairs. This is, in fact, how most
mathematicians think of functions, and how
they are formalized in set theory. 
-/

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

/-
A relation is just a predicate on
two arguments. To convert a relation,
here denoted by ≺, to a set, we use 
set comprehension notation ro build 
a the set of pairs that satisfy the 
predicate defined by the relation. 
-/
def 
relation_to_set_of_tuples: set (β × β) :=
    { p : β × β | p.1 ≺ p.2 }

/-
Given a set of pairs, we can convert
that to a relation, namely one that 
is true for x and y iff (x, y) is in 
the given set.
-/
def set_of_tuples_to_relation: 
  set (β × β) → (β → β → Prop) 
:=
begin
  assume s,
  exact (λ x y, (x, y) ∈ s),
end

variable aSet : set (β × β)
#check set_of_tuples_to_relation aSet
#check relation_to_set_of_tuples(set_of_tuples_to_relation aSet)

example : 
∀ s : set (β × β),
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

/- SULLIVAN STOPPED HERE -/

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
  exact λ (x y: β), 
    ∃(b: β), (x ≺ b) ∧ (b ≺ y)
end

/-
Transitive closure. 

The transitive closure of a relation, R, 
is the union of R and all of its successor relations.
-/

end relation_2102_sec

end relation_2102_ns