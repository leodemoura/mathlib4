import Mathlib.Algebra.Ring.Basic

structure Duration2 where
  val : Int
deriving DecidableEq, Ord, Repr

instance : Add Duration2 where
  add a b := ⟨a.val + b.val⟩

@[simp]
theorem Duration2.add_def (a b : Duration2) : a + b = ⟨a.val + b.val⟩ := rfl

theorem Duration2.val_eq_of_eq : ∀ {d1 d2 : Duration2} (h : d1 = d2), d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem Duration2.eq_of_val_eq : ∀ {d1 d2 : Duration2} (h : d1.val = d2.val), d1 = d2
| ⟨_⟩, _, rfl => rfl

instance (n : Nat) : OfNat Duration2 n where
  ofNat := ⟨n⟩

@[simp] theorem Duration2.zero_def : (0 : Duration2).val = (0 : Int) := by rfl

instance : AddCommSemigroup Duration2 := {
  add_assoc := fun a b c => by simp [Duration2.add_def, AddSemigroup.add_assoc]
  add_comm := fun a b => by simp [Duration2.add_def]; exact AddCommSemigroup.add_comm (A := Int) _ _
}

instance : AddMonoid Duration2 where
  add_zero := by simp [Duration2.eq_of_val_eq, Duration2.add_def, add_zero]
  zero_add := by simp [Duration2.eq_of_val_eq, Duration2.add_def, zero_add]
  nsmul_zero' := fun x => by simp only [nsmul_rec]
  nsmul_succ' := fun x y => by simp only [nsmul_rec]
