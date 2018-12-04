/-
We can import definitions from another
file. Here we import our definitions from
the mynat.lean file. The dot (.) tells 
Lean to look for that file in the same
directory  as this file.
-/
import .mynat

/-
Open the mynat namespace (in that file)
so that we don't have to prefix names 
with mynat.
-/
open mynat


-- Create a namespace for this file
namespace my_list_adt

/-
We now introduce a type of "lists that
contain objects of some other type, T."
For example, an object of type "my_list 
ℕ" would represent a list of value of
type ℕ, while an object of type "my_list
bool" would represent a list of values
of type bool. Here's the "inductive" 
declaration. Notice that, in constrast
to nat and bool, this declaration has
a parameter, T. 
-/

inductive my_list (T: Type) : Type

/-
Now think about the type of my_list. Its
type is Type → Type. We call my_list a 
type constructor or a polymorphic type. 
It takes a type as an argument and then
returns a type, specialized for elements
of the given type, as a result. 

Generic types in Java and template types
in C++ similarly take type parameters and
yield new types specialized for handling
of values of the specified argument type.

Now we give the constructors for our 
polymorphic type. The first one, my_nil,
is a constant term of type (my_list T). 
We will interpret it as representing the 
"empty list of values of type T.""
-/

| nil: my_list

/-
And here's the interesting part. We now
provide my_cons as a constructor used to
produce a bigger list from a given list
by tacking a new value onto its front. 

The constructor takes a value, h (short 
for "head"), of type T, the value to be 
tacked on; and then it takes a value, t 
(short for tail), the smaller list onto
which h will be tacked. The result is a
new my_list, represented by the term, 
(my_cons h t), which we interpret as the
list starting with h as the value at its
head, wand ith the whole smaller list, 
t, as its tail (the rest of the list).
-/

| cons: T → my_list → my_list 

open my_list


/-
EXAMPLES: 
* list of mynat
* list of ℕ
* list of bool
-/

-- some lists of mynat values

def empty_mynat_list : my_list mynat := 
    (nil mynat) -- []

#reduce empty_mynat_list

def zero_mynat_list := 
    (cons zero empty_mynat_list) -- [0]

#reduce zero_mynat_list

def one_mynat_list :=
    (cons one zero_mynat_list) -- [1,0]

#reduce one_mynat_list

def two_mynat_list :=
    (cons two one_mynat_list) -- [2,1,0]

-- A list of ℕ values! [2,1,0]

def two_nat_list :=
    (cons 2 
    (cons 1 
    (cons 0 
    (nil ℕ))))

#reduce two_nat_list


-- A list of bool values [tt,ff,tt]

def a_bool_list :=
    (cons tt
    (cons ff 
    (cons tt 
    (nil bool))))

/-
Adding functions to our algebra
-/

-- If list is empty return true else false
def isNil { T : Type } (l : my_list T) : bool :=
    match l with
    | (nil T) := tt
    | _ := ff
    end

#reduce isNil a_bool_list
#reduce isNil empty_mynat_list

/-
Note that T is an implicit parameter here. Lean
can infer T from l.
-/

-- Length of l. A recursive function.
def length : ∀ { T : Type }, my_list T → ℕ 
| _ (nil T) := 0
| _ (cons h t) := 1 + (length t)

/-
In the pattern matches here, Lean requires 
that we match on both arguments, but we do
not want to give a new name to T, so we use
_ as a wildcard. We can then use the T that
is declared on the first line as a value in
the pattern for the nil list.
-/

#reduce length empty_mynat_list
#reduce length a_bool_list

-- Append two lists

def append : 
    ∀ { T : Type }, 
        my_list T → my_list T → my_list T
| _ (nil T) l2 := l2
| _ (cons h t) l2 := cons h (append t l2)


#reduce a_bool_list
#reduce append a_bool_list a_bool_list



/-
PROOFS!
-/

-- Here's one, no induction needed
theorem nil_append_left_zero :
    ∀ { T : Type },
    ∀ l2 : my_list T,
    append (nil T) l2 = l2 := 
begin
intro T,
intro l2,
-- simplify using rules for append
simp [append],  
end

-- But this requires induction
theorem nil_append_right_zero :
    ∀ { T : Type },
    ∀ l1 : my_list T,
    append l1 (nil T) = l1
:=
begin
intro T,
intro l1,
induction l1,

-- base case
simp [append],

-- inductive case
simp [append],
assumption,
end


-- A desired property of append!

theorem append_length :
    ∀ { T : Type },
    ∀ l1 l2 : my_list T,
    length (append l1 l2) = 
    (length l1) + (length l2) :=
begin
intros T l1 l2,
--cases l1 with h l1' --no work!
induction l1 with h l1 ih, -- need ih

/-
base case: simplify using 
definitions of length, append
-/
simp [append, length],

-- inductive case

-- simplify goal as usual
simp [append, length],

-- critical: rewrite using ih!!!
rw ih,

/-
See if Lean can figure out to
figure out to apply commutativity 
of addition.  
-/
simp,

-- yay, qed!
end

end my_list_adt