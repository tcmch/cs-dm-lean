
#print nat.less_than_or_equal

example : 7 <= 19 :=
begin
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.refl,
end

example : 7 <= 19 :=
begin
repeat { 
  apply nat.less_than_or_equal.step;
  try  { apply nat.less_than_or_equal.refl } 
},
end

#print gt
#print nat.lt

example : ∀ n : ℕ, nat.succ n > n :=
begin
intro n,
unfold gt,
apply nat.less_than_or_equal.refl,
end

#print nat.add_succ

lemma foo : 
  ∀ n m, nat.succ (n + m) = n + nat.succ m :=
begin
  intros n m,
  apply eq.symm,
  rw nat.add_comm,
  simp,
end

theorem sum_inequality (a b : nat) : 
  a > b → a + a > b + b :=
begin
intro h,
change b < a at h,
change nat.succ b <= a at h,
change b + b < a + a,
change nat.succ (b + b) <= a + a,
induction h,

rewrite nat.add_succ,
simp [nat.add],
rewrite foo,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.refl,


end