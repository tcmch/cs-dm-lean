#reduce { 2, 4 } ⊆ { n : ℕ | ∃ m, n = 2 * m }

example : { 2, 4 } ⊆ { n : ℕ | ∃ m, n = 2 * m } := 
begin
change ∀ ⦃a : ℕ⦄, a = 4 ∨ a = 2 ∨ false → (∃ (m : ℕ), a = nat.mul 2 m),
intro,
assume h,
cases h with four rest,
apply exists.intro 2,
assumption,

cases rest with two f,
apply exists.intro 1,
assumption,

contradiction,
end
