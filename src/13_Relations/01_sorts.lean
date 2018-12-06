/-
Every type in Lean in an expression of 
type "Sort u" for some type universe, u.
Prop is just a shorthand for Sort 0, and
Type, for Type 0, which is Sort 1.
-/

-- Sort 0 is Prop (itself of type, Type 0)
#check Sort 0

-- Sort 1 is Type (itself of type, Type 1)
#check Sort 1

-- Sort 2 is Type 1 (itself of type, Type 2)
#check Sort 2


/-
A proposition is a type. Its type is
Prop. Prop is a nice name for Sort 0. 
All of the usual programming types, 
such as bool, int, and string are of 
type, Type. Type is a short name for
Type 0, which in turn is a nice name
for Sort 1. The type of Prop, which 
is Sort 0, is Type, which is Type 0,
which is Sort 1. So the type of Sort
0 is Sort 1, and as you might guess,
the type of Sort n is Sort n + 1.
-/

universes u v
#check Sort 0
#check Sort 1
#check Sort u
