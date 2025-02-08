import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  apply le_trans
  apply inf_le_left
  apply inf_le_left
  apply le_inf
  apply le_trans
  apply inf_le_left
  apply inf_le_right
  apply inf_le_right
  apply le_inf
  apply le_inf
  apply inf_le_left
  apply le_trans
  apply inf_le_right
  apply inf_le_left
  apply le_trans
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  apply le_sup_left
  apply le_trans le_sup_left
  apply le_sup_right
  apply le_trans le_sup_right
  apply le_sup_right
  apply sup_le
  apply le_trans le_sup_left
  apply le_sup_left
  apply sup_le
  apply le_trans le_sup_right
  apply le_sup_left
  apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  apply le_refl
  apply inf_le_left
  apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h (a ⊔ b) a c]
  rw [inf_comm (a ⊔ b)]
  rw [inf_comm (a ⊔ b)]
  rw [absorb1]
  rw [h]
  rw [← sup_assoc]
  rw [inf_comm c a]
  rw [absorb2]
  rw [inf_comm c b]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h (a ⊓ b)]
  rw [sup_comm (a ⊓ b)]
  rw [sup_comm (a ⊓ b)]
  rw [absorb2]
  rw [h]
  rw [← inf_assoc]
  rw [sup_comm c a]
  rw [sup_comm c b]
  rw [absorb1]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem thing1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [sub_eq_add_neg]
  rw [← sub_self a]
  rw [sub_eq_add_neg]
  rw [add_comm]
  rw [add_comm b]
  apply add_le_add_left h

theorem thing2 (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← add_sub_cancel_left a b, add_sub_assoc]
  apply add_le_add_left h

theorem thing3 (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  apply thing2
  rw [← sub_mul]
  apply mul_nonneg
  apply thing1
  exact h
  exact h'
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  apply nonneg_of_mul_nonneg_left
  rw [mul_two]
  nth_rw 2 [dist_comm x y]
  rw [← dist_self x]
  exact dist_triangle x y x
  norm_num

end

-- Direct proof of 0 < 2
def h := Mathlib.Meta.NormNum.isNat_lt_true
  (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 0))
  (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2))
  (Eq.refl false)
