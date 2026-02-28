import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic

open Multiset
variable {α β : Type} {s t u m n : Multiset α} {a b : α}

lemma submultiset_cancelation [DecidableEq α] (h : t ≤ s) : t + (s - t) = s := by
  induction s, t using Quot.induction_on₂ with
  | h s t => simp_all [List.subperm_ext_iff, List.subperm_append_diff_self_of_count_le]

@[simp]
theorem cons_sub_of_not_mem [DecidableEq α] (s : Multiset α) (h : a ∉ t) :
    (a ::ₘ s) - t = a ::ₘ (s - t) := by
  induction s, t using Quot.induction_on₂ with
  | h s t => simp_all [List.cons_diff_of_not_mem h]

lemma disjoint_sub_add_comm [DecidableEq α] (h : Disjoint t u) : s + t - u = s - u + t := by
    induction' t using Multiset.induction_on with a t' h <;> simp_all

lemma disjoint_sub_add_sub_add_comm {m b a d c : Multiset α} [DecidableEq α]
  (d₁ : Disjoint b c) (d₂ : Disjoint d a) : m - c + d - a + b = m - a + b - c + d := by
  simp_all [←inter_eq_zero_iff_disjoint, disjoint_sub_add_comm d₁, disjoint_sub_add_comm d₂]
  rw [←Multiset.sub_add_eq_sub_sub, Multiset.add_comm c a, Multiset.sub_add_eq_sub_sub,
     Multiset.add_assoc, Multiset.add_comm d b, Multiset.add_assoc]

lemma le_of_le_add_of_disjoint [DecidableEq α] (d : Disjoint s u) (h : s ≤ t + u) : s ≤ t := by
  induction' u using Multiset.induction_on with a
  · simp_all
  · obtain := erase_le_erase a h; simp_all

lemma le_of_mem [DecidableEq α] (h : a ∈ m) (n : Multiset α) : ({a} + n)  ≤ m + n := by
  apply (le_iff_count).mpr
  intro x
  rw [← one_le_count_iff_mem] at h
  repeat rw [count_add]
  have h1 : count x {a} ≤ count x m := by by_cases h : (x = a) <;> simp_all
  simp
  exact h1

lemma le_of_le_sub_le_sub [DecidableEq α] (h₁ : s ≤ t - u) (h₂ : u ≤ t) : u ≤ t - s := by
  have ⟨v, vh⟩  := Iff.mp le_iff_exists_add h₁
  have ⟨v', v'h⟩ := Iff.mp le_iff_exists_add h₂
  rw [le_iff_exists_add]
  exists v
  simp_all
  rw [Multiset.add_comm, Multiset.add_sub_cancel_right] at vh
  rw [Multiset.add_comm, Multiset.add_comm, Multiset.add_sub_assoc, vh, Multiset.add_comm s,
  Multiset.add_sub_cancel_right]
  exact le_of_le_of_eq h₁ (id (Eq.symm vh))

@[simp]
def lift_fun_on_mul (f : α → Multiset β) (n : Multiset α) : Multiset β :=
  let ff : α → Multiset β → Multiset β := fun x y => f x + y
  have H :  LeftCommutative ff := by
    substs ff
    exact { left_comm := by intros a1 a2 b; rw [← Multiset.add_assoc,←Multiset.add_assoc,
    Multiset.add_comm (f a1) (f a2)] }
  Multiset.foldr ff 0 n

lemma nodup_sub_of_nodup [DecidableEq α] (n : Multiset α)
    (hm : m.Nodup) : (m - n).Nodup := by
  refine nodup_iff_count_le_one.mpr ?_
  intro a
  obtain h₁ := (nodup_iff_count_le_one.mp hm a)
  have : count a (m - n) ≤ count a m := by simp
  exact this.trans h₁
