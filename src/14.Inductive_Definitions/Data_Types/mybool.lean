namespace my_bool

inductive mybool : Type
| mytt : mybool
| myff : mybool

/-
We declare mybool to be an 
inductively defined type:
a value of type, Type. 

The set of values of this 
type that can be constructed 
is defined by the available 
constructors.

Here there are just two, 
mytt and myff, neither having 
any arguments, so these are
the only two values of this 
type: mytt and myff.
-/

-- We open the mybool namespace
open mybool

#check mytt

/-
With this data type in hand,
we can now define an "algebra"
involving such values. This will
be out little implementation of
Boolean algebra. 

First we'll define the unary
functions involving values of
this type only. Then we'll do
a few binary functions, leaving
you a few more as exercises.
-/

/- Unary Operations -/

-- id_mybool returns what it's given
def id_mybool (b: mybool) : mybool := b

-- true_mybool always returns true
def true_mybool (b: mybool) := mytt

-- false_mybool always returns false
def false_mybool (b: mybool) := myff

-- not_mybool returns the other value
def not_mybool (b: mybool) :=
    match b with 
    | mytt := myff
    | myff := mytt
    end

/-
The match command does a kind of case
analysis on b. b, being of type, mybool,
can only have been "built" by the mytt
or myff constructors. In the first case,
the function returns myff. In the latter
case, it returns mytt.
-/

-- look, it works
#reduce id_mybool myff
#reduce id_mybool mytt
#reduce not_mybool myff
#reduce not_mybool mytt

/-
EXERCISE: use #reduce to test the other
two functions (false_ and true_mybool).
-/

/-
So we've just defined a data type and
some operations on values of this type.
Do our operations capture what we want,
which is to implement Boolean algebra?
Let's "verify" our software by proving
a proposition that we think should be
true: that if you apply not_mybool to 
a value, b, of type mybool and apply it
again to the result, we should get back
to b. 
-/

theorem not_inverse : 
    ∀ b : mybool, 
        not_mybool (not_mybool b) = b :=
begin
    intro b,
    cases b,
    apply rfl,
    apply rfl,
end

/-
That's amazing. We didn't "test" our
software by running it with various
inputs. Rather we proved a fact about
its behavior on *all* possible values
of its inputs using logic.
-/

/-
Here's a binary function, and_mybool,
taking two mybools and returning one
as a result. We intend this function 
to implement the Boolean and operator.
-/

def and_mybool' (b1 b2 : mybool) : mybool :=
match b1, b2 with
    | mytt, mytt := mytt
    | mytt, myff := myff
    | myff, mytt := myff
    | myff, myff := myff
end

/-
The new concept here is that we can match
on several arguments. 
-/

/-
We notice that all of the combinations of
input values after mytt and mytt return
myff. We can use "wildcards" in matches to
match any value. Matches are attempted in
the order in which rules appear in code.
(It's important to try to match mytt, mytt
before applying the wildcarded rule! Why?)
-/

def and_mybool (b1 b2 : mybool) : mybool :=
match b1, b2 with
    | mytt, mytt := mytt
    | _, _ := myff
end

/-
EXERCISE: Now you should implement each of 
the following Boolean operators:

- or, as or_mybool
- implies, as implies_mybool
-/

/-
EXERCISE: To test that you have given
valid implementations, state and prove 
the propositon that for any values, b1
and b2, not_mybool (and_mybool b1 b2) =
or_mybool (not_mybool b1) (not_mybool b2).
-/

def or_mybool (b1 b2 : mybool) : mybool :=
match b1, b2 with
    | myff, myff := myff
    | _, _ := mytt
end

theorem demorgan1 : ∀ b1 b2 : mybool, 
    not_mybool 
        (and_mybool b1 b2) 
    =
    or_mybool 
        (not_mybool b1) 
        (not_mybool b2) :=
begin
    intros,
    cases b1,
    cases b2,
    apply rfl,
    apply rfl,
    cases b2,
    apply rfl,
    apply rfl,
end

/-
EXERCISE: State and prove the other 
DeMorgan Law for Boolean algebra.
-/

theorem demorgan2 : ∀ b1 b2 : mybool, 
    not_mybool 
        (or_mybool b1 b2) 
    =
    and_mybool 
        (not_mybool b1) 
        (not_mybool b2) :=
begin
    intros,
    cases b1,
    cases b2,
    apply rfl,
    apply rfl,
    cases b2,
    apply rfl,
    apply rfl,
end

end my_bool