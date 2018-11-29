namespace my_nat

inductive mynat : Type 
| zero : mynat
| succ : mynat → mynat

def zero := mynat.zero
def one := mynat.succ zero
def two := mynat.succ one
def three := 
    mynat.succ 
        (mynat.succ 
            (mynat.succ 
                zero))

#reduce one
#reduce two
#reduce three

/-
Unary functions
-/

-- identity function on mynat
def id_mynat (n: mynat) := n

-- constant zero function
def zero_mynat (n: mynat) := zero

-- predecessor function
def pred (n : mynat) :=
    match n with
    | mynat.zero := zero
    | mynat.succ n' := n'
    end

/-
There are two new and important
concepts here. The first is a new
kind of matching. The second is
that we define the predecessor 
of zero to be zero. That's a bit
odd.

Look at the matching. The first
pattern is familar. The second,
though, it interesting. If we get
here, we know n isn't zero, so it
must by the successor of the next
smaller mynat. Here we give that
next smaller value the name n'.
And of course that's the number
we want to return as precessor!
-/

/- 
Now let's see binary operations
and recursive functions. To 
define a recursive function we
have a new syntax/
-/

def add_mynat: mynat → mynat → mynat
| mynat.zero m := m
| (mynat.succ n') m :=
    mynat.succ (add_mynat n' m)

/-
Syntax notes: use explicit function
type syntax. Omit any :=. Define how
the function works by cases. Each case
defines what the function does for the
specific kinds of arguments used in the
case. Omit commas between arguments
All cases may be covered
-/

-- It works!
#reduce add_mynat one two
#reduce add_mynat three three


/-
EXERCISES:

(1) We just implemented addition as
the recursive (iterated) application
of the successor function. Now you are
to implement multiplication as iterated
addition.

(2) Implement exponentiation as iterated
multiplication.

(3) Take this pattern one ste further.
What function did you implement? How
would you write it in regular math 
notation?
-/

/-
We can easily prove that for all m : ℕ, 
add_mynat 0 m = m, because the definition
of add_mynat has a matching pattern (the
first one), which explains exactly how to
reduce a term with first argument zero.
-/

theorem zero_left_id: 
    ∀ m : mynat, 
        add_mynat mynat.zero m = m
:=
begin
intro m,
simp [add_mynat],
end

/-
We just asked Lean to simplify the
goal using the "simplication rules"
specified by the two cases in the  
definition of add_mynat. The result
is m = m, which Lean takes care of
with an automated application of rfl.
-/

/-
Unfortunately, we don't have such 
a simplification rule when the zero
is on the right! For that we need a
whole new proof strategy: proof by
induction.
-/

theorem zero_right_id : 
    ∀ m : mynat, 
        add_mynat m mynat.zero = m
:=
begin
    intro m,
    induction m with m' h,

    -- base case
    simp [add_mynat],

    -- inductive case
    simp [add_mynat],
    assumption,
end

/-
Proof by induction is proof by
case analysis on the *constructors*
for values of a given type. If we 
show that some predicate involving
a natural number, n, is true no matter 
what *constructor* was used to "build"
n, then we've' shown the predicate to
be true for *all* (∀) values of that 
type.

Let's think about the two
constructors for values of type
mynat. First, there is the zero 
constructor.  That's the "base 
case". Second, there's the succ
constructor. From a value, n, 
is constructs a value succ n.

Now if we prove the following two
cases, we're done:

(1) the predicate in question is
true when n is zero

(2) if the predicate is true for
n, then it is true for succ n.

The reason we're done is that 
there are no other possibilities
for n.

The set of values of an inductively 
defined type is defined to be exactly 
the set of values that can be built 
by using the available constructors 
any *finite* number of times, and
that there are no other values of 
the given type.
-/

/-

-/

/-
EXERCISE: try this proof using
cases instead of induction. Cases
also does case analysis on the
constructors. Why does simple case 
analysis fail?
-/

/-
EXERCISES: To Come Shortly
-/

end my_nat