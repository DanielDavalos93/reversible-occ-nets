import PetriNet.Nets
import PetriNet.MultisetAux
import Mathlib.Data.Set.Disjoint
import Mathlib.Logic.Relation
import Mathlib.Data.Multiset.Basic
open Nets
open Relation Relation.TransGen
open Multiset
open Sum

/-!
This file provides the definitions and properties necessary to construct a flow
relationship in a Petri net. Which is necessary to establish occurrence nets.

`<` is a relationship between places and transitions directly.
Their transitive closure `≺ ` [abr: \pre, \prec] is given by `TransGen`.
Their reflexo-transitive closure `≼ ` [abr: \prece, \preceq] is given by `ReflTransGen`.

A marked net (N, m₀) could be think as a tuple (α, β, •_, _•, m₀).
This is helpful at time to defined the flow relationship, because we can have x,y ∈ α ⊎ β
with x ≼ y (for instance) regardless of whether x and y are the same type or not. This
disjoint union we write as `α ⊕ β`.

## Notation

  * If N is a `Net α β`, and you want to write that x ≺ y, you need to establish whether
  x and y are places or transitions.
  For example, if `x : β` and `y : α`, then x ≺  y is equivalent to
  `inr x ≺⦃N⦄ inl y`. It's not necessary that x and y must be of different types,
  we can have `x y : β` and `Sum.inr x ≺⦃N⦄ Sum.inr y`, since is a transitive closure.
  Trichotomy is not true over this transitive closure.
  * If two transitions t₁ and t₂ are in inmediate conflict, we write `t₁ #₀⦃N⦄ t₂`.
  * If x and y are in conflict: `x #⦃N⦄ y`. This is an extend definition from the inmediate
  conflict.
  * `x co⦃N⦄ y` is an abreviature of the concurrency between x and y.

## Standard variable for types/general structures
  * `O : is_occurrence N`, if `N : Net α β`
  * `MO : is_marked_occurrence M`, if `M : MarkedNet α β`
-/


variable {α : Type} {β : Type} {a : α} {t t' t'' : β}
variable {N : Net α β}
variable {w x y z : α ⊕ β}
variable {m m' m'' : Multiset α}
variable {X Y : Multiset (α ⊕ β)}

namespace Flow

section Immediate

def immediate (N : Net α β) : (α ⊕ β) → (α ⊕ β) → Prop
  | inl p, inr t  =>  p ∈ •⦃N⦄ t
  | inr t, inl p  =>  p ∈  t•⦃N⦄
  | _, _          => false

notation:200  l:201 " <⦃" N "⦄ " r:202 => immediate ↑N l r

lemma lt_of_mem_pre (_ : a ∈ •⦃N⦄t) : inl a <⦃N⦄ inr t := by
  unfold immediate; simp_all

lemma lt_of_mem_post (_ : a ∈ t•⦃N⦄) : inr t <⦃N⦄ inl a := by
  unfold immediate; simp_all

lemma mem_pre_of_lt (_ : inl a <⦃N⦄ inr t) : a ∈ •⦃N⦄ t := by
  unfold immediate at *; simp_all

lemma mem_post_of_lt (_ : inr t <⦃N⦄ inl a) : a ∈ t•⦃N⦄ := by
  unfold immediate at *; simp_all


lemma not_exists_inl_lt_inl (a : α) : ¬ ∃ b, inl b <⦃N⦄ inl a := by
  unfold immediate; simp

lemma not_exists_inl_gt_inl (a : α) : ¬ ∃ b, inl a <⦃N⦄ inl b := by
  unfold immediate; simp

lemma not_exists_inr_lt_inr (t : β) : ¬ ∃ t', inr t <⦃N⦄ inr t' := by
  unfold immediate; simp

lemma not_exists_inr_gt_inr (t : β) : ¬ ∃ t', inr t' <⦃N⦄ inr t := by
  unfold immediate; simp

lemma exists_eq_inr_of_gt_inr (_ : inl a <⦃N⦄ x) : ∃ t, x = inr t := by
  cases x with
  | inl _ => have := not_exists_inl_lt_inl (N := N) a; contradiction
  | inr t => exists t

lemma exists_eq_inr_of_lt_inl (_ : x <⦃N⦄ inl a) : ∃ t, x = inr t := by
  cases x with
  | inl _ => have := not_exists_inl_lt_inl (N := N) a; contradiction
  | inr t => exists t

lemma exists_eq_inl_of_gt_inr (_ : inr t <⦃N⦄ x) : ∃ a, x = inl a := by
  cases x with
  | inl t => exists t
  | inr  => have := not_exists_inr_lt_inr (N := N) t; contradiction

lemma exists_inl_lt_of_inr (t : β) : ∃ a, inl a <⦃N⦄ inr t := by
  obtain ⟨a, _⟩ := exists_mem_of_ne_zero <| (N.cons_prod t).left
  exists a

lemma exists_eq_inl_of_lt_inr (h : x <⦃N⦄ inr t) : ∃ a, x = inl a ∧ (a ∈ •⦃N⦄ t) := by
  by_contra!; unfold immediate at h
  cases x with
  | inl val => simp_all only
  | inr _ => simp at h


lemma not_mem_pre_of_lt_post {b} (h : x <⦃N⦄ inl b) (a : α) (hx : x = inl a) :
    a ∉ presetₜ N t :=  by
  have h := not_exists_inl_gt_inl (N := N) a
  simp_all only [not_exists]

lemma not_lt_of_minimal (h : a ∈ minimal N) (x : α ⊕ β) : ¬ (x <⦃N⦄ inl a) := by
  intro hx
  obtain ⟨t, _⟩ := exists_eq_inr_of_lt_inl hx
  simp_all [minimal, presetₚ, immediate]
  contrapose! h
  simp [Set.Nonempty]
  exists t

end Immediate

section Causal

def causal (N : Net α β) : (α ⊕ β) → (α ⊕ β) → Prop :=
  TransGen (immediate N)

notation:200 l:50 " ≺⦃" N "⦄ " r:202 => causal ↑N l r

lemma causal_of_mem_pre (h : a ∈ •⦃N⦄t) : inl a ≺⦃N⦄ inr t := by
  unfold causal; exact single h

lemma causal_of_mem_post (h : a ∈ t•⦃N⦄) : inr t ≺⦃N⦄  inl a := by
  unfold causal; exact single h

lemma causal_of_mem_pre_mem_post {b} (ha : a ∈ •⦃N⦄t) (hb : b ∈ t•⦃N⦄) :
    inl a ≺⦃N⦄ inl b :=
  .trans (causal_of_mem_pre ha) (causal_of_mem_post hb)

lemma split_causal_of_non_disjoint_pre_post (d : ¬ Disjoint t•⦃N⦄ (•⦃N⦄t')) :
    ∃ a, (inr t ≺⦃N⦄ inl a) ∧ (inl a ≺⦃N⦄ inr t')  := by
  simp [disjoint_left] at d
  obtain ⟨a, pre, post⟩ := d
  exists a
  exact ⟨causal_of_mem_post pre, causal_of_mem_pre post⟩

lemma causal_of_lt (i : x <⦃N⦄ y) : (x ≺⦃N⦄ y) := by
  simp_all [causal]; exact single i

end Causal


section Preorder

def preorder (N : Net α β) : (α ⊕ β) → (α ⊕ β) → Prop :=
  ReflTransGen (immediate N)

notation:65 l:65 " ≼⦃" N "⦄ " r:66  => preorder ↑N l r

lemma preorder_ref (x : α ⊕ β) : x ≼⦃N⦄ x := by
  unfold preorder; simp [IsRefl.refl]

lemma preorder_trans (h1 : x ≼⦃N⦄ y) (h2 : y ≼⦃N⦄ z) : x ≼⦃N⦄ z := by
  simp_all [preorder]; exact IsTrans.trans x y z h1 h2

lemma preorder_of_lt : x <⦃N⦄ y → x ≼⦃N⦄ y :=
  .tail .refl

@[simp] lemma preorder_of_causal : x ≺⦃N⦄ y → x ≼⦃N⦄ y :=
  to_reflTransGen

lemma preorder_of_mem_pre (h : a ∈ •⦃N⦄t) : inl a ≼⦃N⦄ inr t :=
  preorder_of_lt h

lemma preorder_of_mem_pos (h : a ∈ t•⦃N⦄) : inr t≼⦃N⦄ inl a :=
  preorder_of_lt h

lemma preorder_of_mem_pre_mem_post {b} (ha : a ∈ •⦃N⦄t) (hb : b ∈ t•⦃N⦄) :
    inl a ≼⦃N⦄ inl b :=
  preorder_of_causal (causal_of_mem_pre_mem_post ha hb)

@[simp] lemma preorder_iff_eq_or_causal : (x ≼⦃N⦄ y) ↔ y = x ∨ (x ≺⦃N⦄ y) :=
  reflTransGen_iff_eq_or_transGen

lemma causal_of_preorder_and_lt {z} (h1 : x ≼⦃N⦄ y) (h2 : y <⦃N⦄ z) : x ≺⦃N⦄ z := by
  rcases preorder_iff_eq_or_causal.mp h1 with _ | h
  · subst x; exact causal_of_lt h2
  · exact .trans h (causal_of_lt h2)

variable {b : α}

lemma flow_of_pre_and_flow (ha : inr t ≼⦃N⦄ inl a) (hb : b ∈ •⦃N⦄t) : inl b ≼⦃N⦄ inl a := by
  obtain h := lt_of_mem_pre hb
  exact .trans (.tail .refl h) ha

lemma not_cause_of_minimal (ha : a ∈ minimal N) (neq : x ≠ inl a) : ¬ (x ≼⦃N⦄ inl a) := by
  intro h
  simp_all [preorder]
  cases h with
  | refl => contradiction
  | @tail c _ _ => obtain := not_lt_of_minimal ha c; contradiction

end Preorder

end Flow

open Flow

section Conflict
def immediate_conflict (N : Net α β) (t t' : β) : Prop :=
  t ≠ t' ∧ ¬ (Disjoint (•⦃N⦄ t) (•⦃N⦄ t'))

notation:60 l:61 " #₀⦃" N:61 "⦄ " r:61 => immediate_conflict ↑N l r
def conflict (N : Net α β) (x y : α ⊕ β) : Prop :=
  ∃ t t' : β, inr t ≼⦃N⦄ x ∧ inr t' ≼⦃N⦄ y ∧ t #₀⦃N⦄ t'

notation:50 l:50 " #⦃" N:50 "⦄ " r:50 => conflict ↑N l r

namespace example_conflict
open Pl Tr
open Flow

example : inl d #⦃N₁⦄ inl e := by
  unfold conflict ; exists t₁, t₂
  have prec₁ : inr t₁ ≼⦃N₁⦄ inl d := by
    apply preorder_of_lt (by unfold N₁ post immediate; simp)
  have prec₂ : inr t₂ ≼⦃N₁⦄ inl e := by
    apply preorder_of_lt (by unfold N₁ post immediate; simp)
  have confl : t₁ #₀⦃N₁⦄ t₂ := by
    unfold immediate_conflict
    constructor
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    · unfold Disjoint N₁ presetₜ pre ; simp
      exists {b}
  exact ⟨prec₁, prec₂, confl⟩

end example_conflict

@[simp] lemma immediate_conflict_symm (h : t #₀⦃N⦄ t') : (t' #₀⦃N⦄ t) := by
  simp_all [immediate_conflict, disjoint_comm]
  obtain ⟨ne, nd⟩ := h
  exact (ne_comm.mp ne)

@[simp] lemma conflict_symm (h : x #⦃N⦄ y) : y #⦃N⦄ x := by
  obtain  ⟨t, t', ⟨_, _, c⟩ ⟩ := h
  have := immediate_conflict_symm c
  exists t', t

@[simp] lemma not_conflict_symm (N : Net α β) (x y : α ⊕ β) (h : ¬ x #⦃N⦄ y) : ¬ y #⦃N⦄ x := by
  intro; simp_all [conflict_symm]

lemma conflict_of_immediate_conflict (h : t #₀⦃N⦄ t') : inr t #⦃N⦄ inr t' := by
  unfold conflict; exists t, t'; simp_all

def immediate_conflict_of_shared_pre (ne : ¬ t = t') (h : ¬ Disjoint (•⦃N⦄ t) (•⦃N⦄ t')) :
    t #₀⦃N⦄ t' := by
  simp_all [immediate_conflict]

lemma immediate_conflict_of_shared_place : ¬ t = t' →  a ∈ •⦃N⦄ t → a ∈ •⦃N⦄ t' → t #₀⦃N⦄ t' := by
  intros; simp_all [immediate_conflict, Disjoint]; exists {a}; simp_all

def conflict_of_shared_pre (ne : ¬ t = t') (h : ¬ Disjoint (•⦃N⦄ t) (•⦃N⦄ t')) :
    inr t #⦃N⦄ inr t' := by
  exists t, t'
  exact ⟨preorder_ref (inr t), preorder_ref (inr t'), immediate_conflict_of_shared_pre ne h⟩

-- Interaction with causality
lemma conflict_inherits_left (c : x #⦃N⦄ y) (f : x ≼⦃N⦄ z) : z #⦃N⦄ y :=  by
  unfold conflict at *
  obtain ⟨t, t', a, _⟩ := c
  obtain := ReflTransGen.trans a f
  exists t, t'

lemma conflict_inherits_right (c : x #⦃N⦄ y) (f : y ≼⦃N⦄ z) : x #⦃N⦄ z :=  by
  unfold conflict at *
  obtain ⟨t, t', _, b, _, _⟩ := c
  obtain := ReflTransGen.trans b f
  exists t, t'

/--
A place has a backward conflict it has more that one transition in its preset.
-/
def backward_conflict (N : Net α β) (a : α) : Prop :=
  ∃ t t' : β, t ≠ t' ∧ inr t <⦃N⦄ inl a  ∧ inr t' <⦃N⦄ inl a

end Conflict

section Acyclicity
/--
A net is acyclic if the causality relation is so.
-/

def acyclic (N : Net α β) : Prop :=
  ∀ x : α ⊕ β, ¬(x ≺⦃N⦄ x)


lemma cycle_from_shared_pre_post (d₁ : ¬Disjoint (t •⦃N⦄) (•⦃N⦄ t'))
    (d₂ : ¬Disjoint (t' •⦃N⦄) (•⦃N⦄ t)) : ¬acyclic N := by
  rw [acyclic, not_forall_not]
  obtain ⟨a, ha, ha'⟩ := split_causal_of_non_disjoint_pre_post d₁
  obtain ⟨_, hb, hb'⟩ := split_causal_of_non_disjoint_pre_post d₂
  exists (inl a)
  exact .trans (.trans ha' hb) (.trans hb' ha)

end Acyclicity

section OccurrenceNet

structure is_occurrence (N : Net α β) where
  acyclicity : acyclic N
  no_self_conflict : (∀ t : β, ¬inr t #⦃N⦄ inr t)
  no_backward_conflict : (∀ a : α, ¬backward_conflict N a)
  set_preset : (∀ t : β,  Nodup (•⦃N⦄ t))
  set_postset : (∀ t : β, Nodup (t •⦃N⦄))

structure is_marked_occurrence (M : MarkedNet α β) : Prop where
  occurrence : is_occurrence M.toNet
  initial_set : Nodup M.m₀
  inital_minimal : ∀ {x}, x ∈ M.m₀ → x ∈ minimal M.toNet

lemma causal_irref (O : is_occurrence N) (_ : x ≺⦃N⦄ y) : ¬(x = y) := by
  obtain := O.acyclicity x; intro; simp_all

lemma causal_asymm (O : is_occurrence N) (h : x ≺⦃N⦄ y) : ¬y ≺⦃N⦄ x := by
  intro h'
  obtain : x ≺⦃N⦄ x := TransGen.trans h h'
  obtain _ := O.acyclicity x
  contradiction

-- Structural properties of Occurrence nets
lemma disjoint_pre_post (O : is_occurrence N) (t : β) : Disjoint  (t •⦃N⦄) (•⦃N⦄ t) := by
  by_contra h
  obtain irr := O.acyclicity (inr t)
  obtain ⟨ _, h1, h2⟩ := split_causal_of_non_disjoint_pre_post h
  obtain := TransGen.trans h1 h2
  contradiction

variable {b c : α}

lemma not_mem_post_of_mem_pre (O : is_occurrence N) (ha : a ∈ •⦃N⦄t) : a ∉ t•⦃N⦄ := by
  obtain h := disjoint_pre_post O t
  unfold Disjoint at h; contrapose! h; exists {a}; simp_all

lemma not_mem_pre_of_mem_pre (O : is_occurrence N) (ha : a ∈ t•⦃N⦄) : a ∉ •⦃N⦄t := by
  contrapose! ha; exact not_mem_post_of_mem_pre O ha

lemma ne_of_mem_pre_mem_post (O : is_occurrence N) (ha : a ∈ •⦃N⦄t) (hb : b ∈ t•⦃N⦄) :
    a ≠ b := by
  have h := causal_of_mem_pre_mem_post ha hb
  have := causal_asymm O h
  by_contra; subst a; contradiction

-- Properties about Immediate
lemma unique_immediate_of_place (O : is_occurrence N) (ha : a ∈ t•⦃N⦄) (h : x <⦃N⦄ inl a) :
    x = inr t := by
  cases x with
  | inl _ =>  obtain := not_exists_inl_lt_inl (N := N) a; simp_all
  | inr t' =>
    obtain _ := lt_of_mem_post ha
    obtain h := O.no_backward_conflict a
    contrapose! h
    exists t', t
    simp_all

lemma unique_pre_from_immediate (O : is_occurrence N) (h1 : inr t <⦃N⦄ inl a)
    (h2 : inr t' <⦃N⦄ inl a) : t = t' := by
  unfold immediate  at *
  obtain h := O.no_backward_conflict a;
  contrapose! h
  exists t, t'

-- Properties of causal
lemma no_causal_of_mem_post (O : is_occurrence N) (ha : a ∈ t•⦃N⦄) : ¬inl a ≼⦃N⦄ inr t:= by
  obtain := causal_asymm O (causal_of_mem_post ha)
  simp_all

lemma no_causal_mem_post_of_mem_pre (O : is_occurrence N) (ha : a ∈ t•⦃N⦄) (hb : b ∈ •⦃N⦄t) :
    ¬ inl a ≺⦃N⦄ inl b :=
  causal_asymm O (causal_of_mem_pre_mem_post hb ha)

lemma no_causal_on_postset (O : is_occurrence N) (ha : a ∈ t•⦃N⦄) (hb : b ∈ t•⦃N⦄) :
    ¬inl a ≺⦃N⦄ inl b := by
  unfold Flow.causal;
  by_contra h
  cases h with
  | single _ => contradiction
  | @tail x _ xCt xCb  =>
    have : x = inr t := unique_immediate_of_place O hb xCb; subst x
    obtain := TransGen.tail xCt (lt_of_mem_post ha)
    obtain ⟨ac, _⟩ := O
    simp_all only [acyclic, Flow.causal, postsetₜ]

-- Properties about preorder
lemma no_preorder_on_postset (O : is_occurrence N) (ne : a ≠ b) (ha : a ∈ t•⦃N⦄)
    (hb : b ∈ t•⦃N⦄) :  ¬inl a ≼⦃N⦄ inl b := by
  simp_all [preorder_iff_eq_or_causal, inl.injEq, not_or, ne_comm]
  exact no_causal_on_postset O ha hb

lemma causal_init (O : is_occurrence N) (h : x ≺⦃N⦄ y) (ht : inr t <⦃N⦄ y) :
    x ≼⦃N⦄ inr t := by
  induction h with
  | @single z hz =>
      obtain ⟨b , hb⟩ := exists_eq_inl_of_gt_inr ht; subst z
      obtain ⟨t', ht'⟩ := exists_eq_inr_of_lt_inl hz; subst x; simp_all
      obtain h := unique_pre_from_immediate O ht hz
      exact Or.symm (Or.inr h)
  | @tail w ww x y ih  =>
      obtain ⟨b , hb⟩ := exists_eq_inl_of_gt_inr ht; subst hb
      obtain ⟨t', ht'⟩ := exists_eq_inr_of_lt_inl y; subst w; simp_all
      obtain := unique_pre_from_immediate O ht y; subst t
      right
      exact x

lemma causal_inr_inr_split (h : inr t ≺⦃N⦄ inr t') :
    ∃ a, inr t ≺⦃N⦄ inl a ∧ inl a ≺⦃N⦄ inr t' := by
  cases h with
  | single h =>
    have := not_exists_inr_lt_inr (N:=N) t
    simp_all
  | tail h' h'' =>
    obtain ⟨a, rfl , c⟩ := exists_eq_inl_of_lt_inr h''
    exists a
    exact ⟨h', causal_of_lt h''⟩

lemma not_mem_pre_of_pre_cause (O : is_occurrence N)
    (hb : inl b <⦃N⦄ inr t') (h : b ∈ presetₜ N t) : ¬ inr t' ≺⦃N⦄ inr t := by
  by_cases heq : (t = t')
  · subst t
    exact O.acyclicity (inr t')
  · by_contra! h'
    obtain ic := immediate_conflict_of_shared_place heq (mem_pre_of_lt h) hb
    have ⟨a, ha, ha'⟩ := causal_inr_inr_split h'
    obtain sc := conflict_inherits_right (conflict_of_immediate_conflict ic) <|
      match ha with
      | single hw =>
          preorder_of_causal (.trans (causal_of_lt hw)  ha')
      | tail hw a =>
          preorder_of_causal (.trans hw (.trans (causal_of_lt a) ha'))
    exact absurd sc (O.no_self_conflict t)

lemma no_causal_of_mem_prea (O : is_occurrence N) (ha : inl a ≺⦃N⦄ inl b) (hb : inl b ≺⦃N⦄ inr t) :
    ¬ a ∈ •⦃N⦄ t := by
  cases ha using Relation.TransGen.head_induction_on with
  | @ single x i =>
    have h := not_exists_inl_gt_inl (N := N) a
    push_neg at h
    exact absurd i (h b)
  | @head x y h1 h2 _ =>
    obtain ⟨t', th⟩ := exists_eq_inr_of_gt_inr (N := N) h1
    subst y
    intro h
    exact absurd (.trans h2 hb) (not_mem_pre_of_pre_cause O h1 h)

lemma no_causal_of_mem_pre (O : is_occurrence N) (ha : a ∈ •⦃N⦄t) (hb : b ∈ •⦃N⦄t) :
    ¬inl a ≺⦃N⦄ inl b:= by
  intro h
  obtain h' := no_causal_of_mem_prea O h (causal_of_mem_pre hb)
  simp_all

-- Properties about conflict
lemma no_conflicts_on_postset (O : is_occurrence N) (ha : a ∈ t•⦃N⦄) (hb : b ∈ t•⦃N⦄) :
     ¬ inl a #⦃N⦄ inl b := by
  simp [conflict,immediate_conflict, Disjoint, preorder]
  intros t₁ t₁FA t₂ t₂Fb ne m le1 le2
  cases t₁FA with
  | @tail x _ hx xIa =>
    cases t₂Fb with
    | @tail y _ c2 d2=>
    obtain : x = inr t := unique_immediate_of_place O ha xIa
    obtain : y = inr t := unique_immediate_of_place O hb d2
    subst x y
    obtain nself := O.no_self_conflict t
    simp [conflict, immediate_conflict, preorder, Disjoint] at nself
    exact nself t₁ hx t₂ c2 ne m le1 le2

lemma no_self_conflict (O : is_occurrence N) : ¬ x #⦃N⦄ x := by
  cases x with
  | inl a =>
    unfold conflict; push_neg; intros t t' tFa t'Fa; simp_all
    cases tFa with
    | single h =>
      obtain := causal_init O t'Fa h
      obtain c := O.no_self_conflict t
      unfold conflict at c; contrapose! c; exists t, t'; simp_all
    | @tail x _ tx xa =>
      obtain ⟨t'', ht⟩ := exists_eq_inr_of_lt_inl xa;
      subst x
      obtain t't'' := causal_init O t'Fa xa
      obtain c := O.no_self_conflict t''
      contrapose! c;
      exact conflict_inherits_right
        (conflict_inherits_left (conflict_of_immediate_conflict c) (preorder_of_causal tx)) t't''
  | inr t => exact O.no_self_conflict t

/-!
In a concurrent set stands for elements that are able to occur concurrently, i.e.,
they are not in conflict, and they do not causally depend on each other.
-/
def concurrent (N : Net α β) (x y : α ⊕ β) : Prop :=
  x ≠ y ∧ ¬(x ≼⦃N⦄ y) ∧ ¬(y ≼⦃N⦄ x) ∧ ¬(x #⦃N⦄ y)

notation:200  l:200 "co⦃" N "⦄ " r:201 => concurrent ↑N l r

@[simp]
lemma co_symm {x y : α ⊕ β} (h : x co⦃N⦄ y) : y co⦃N⦄ x := by
  unfold concurrent;
  obtain ⟨ne, _, _, nocf⟩ := h
  obtain := not_conflict_symm N x y nocf
  symm at ne
  simp_all [ne_eq, not_false_eq_true, and_self]

lemma concurrent_from_same_preset (O : is_occurrence N)
    (ne : a ≠ b) (ha : a ∈ •⦃N⦄t) (hb : b ∈ •⦃N⦄t) : inl a co⦃N⦄ inl b := by
  unfold concurrent
  have h1 := no_causal_of_mem_pre O ha hb
  have h2 := no_causal_of_mem_pre O hb ha
  obtain ha : inl a ≺⦃N⦄  inr t := causal_of_mem_pre ha
  obtain hb : inl b ≺⦃N⦄  inr t := causal_of_mem_pre hb
  obtain nself := O.no_self_conflict t
  simp_all [ne_comm, conflict, immediate_conflict]
  intro t1 ht1 t2 ht2 neq
  contrapose! nself
  refine ⟨t1, ?_, ⟨t2, ⟨?_,⟨neq, nself⟩⟩⟩⟩
  · right
    exact .trans ht1 ha
  · right
    exact .trans ht2 hb

lemma concurrent_from_same_postset (O : is_occurrence N)
    (ne : a ≠ b) (ha : a ∈ t•⦃N⦄) (hb : b ∈ t•⦃N⦄) : inl a co⦃N⦄ inl b := by
  unfold concurrent
  repeat' constructor
  · intro h; obtain := Sum.inl.inj h; contradiction
  · exact no_preorder_on_postset O ne ha hb
  · exact no_preorder_on_postset O (ne_comm.mpr ne) hb ha
  · exact no_conflicts_on_postset O ha hb

lemma no_conflict_of_concurrent (h : x co⦃N⦄ y) : ¬(x #⦃N⦄ y) := by
  unfold concurrent at *; contrapose! h;
  obtain ⟨t, t', _⟩ := h; intros; exists t, t'

def concurrent_set (N : Net α β) (X : Multiset (α ⊕ β)) : Prop :=
  Nodup X ∧ (∀ {x y : α ⊕ β}, x ∈ X → y ∈ X → x ≠ y → x co⦃N⦄ y)

def Concurrent (N : Net α β) (m : Multiset α) : Prop :=
  (Nodup m) ∧ (∀ {x  y: α }, (x ∈ m) → (y ∈ m) → x ≠ y → inl x co⦃N⦄ inl y)

lemma no_concurrent_of_mem_pre_mem_post (O : is_occurrence N) (ha : a ∈ m) (hb : b ∈ m)
    (ha' : a ∈ •⦃N⦄t) (hb' : b ∈ t•⦃N⦄) : ¬ Concurrent N m := by
  obtain := causal_of_mem_pre_mem_post ha' hb'
  unfold Concurrent concurrent;
  by_contra h;
  obtain h := h.right
  specialize h ha hb (ne_of_mem_pre_mem_post O ha' hb')
  simp_all

variable [DecidableEq α]
lemma post_disjoint_of_contains_pre (O : is_occurrence N)
  (C : Concurrent N m) (e : (•⦃N⦄t) ≤ m) : Disjoint m (t•⦃N⦄) := by
  by_contra d
  obtain ⟨a, ha⟩ := exists_mem_of_ne_zero (N.cons_prod t).1
  obtain ⟨b, hb, hb'⟩ : ∃ a, a ∈ m ∧ a ∈ t•⦃N⦄ := by
    rw [Multiset.disjoint_left] at d; simp_all
  obtain := no_concurrent_of_mem_pre_mem_post O (mem_of_le e ha) hb ha hb'
  contradiction

lemma pre_disjoint_of_contains_post (O : is_occurrence N)
  (C : Concurrent N m) (e : (t•⦃N⦄) ≤ m) : Disjoint m (•⦃N⦄t) := by
  unfold Concurrent at C; contrapose! C; intro d
  obtain ⟨a, ha₁, ha₂⟩ := exists_mem_of_ne_zero (mt inter_eq_zero_iff_disjoint.mp C)
                |>.imp (fun _ => mem_inter.mp)
  obtain ⟨b, hb⟩ := exists_mem_of_ne_zero (N.cons_prod t).right
  have := Multiset.mem_of_le e hb
  exists a , b
  have : a ≠ b := ne_of_mem_pre_mem_post O ha₂ hb
  have : inl a ≼⦃N⦄ inl b := preorder_of_causal <| causal_of_mem_pre_mem_post ha₂ hb
  simp_all [concurrent]

lemma no_concurrent_of_contains_cause_post (O : is_occurrence N) (en : •⦃N⦄t ≤ m)
    (ha : a ∈ m - •⦃N⦄t) (hb : b ∈ t•⦃N⦄) (h : inl a ≺⦃N⦄ inl b) :
    ¬ Concurrent N m := by
  cases h with
  | single => contradiction
  | @tail x _ hx hx' =>
    obtain : x = inr t := unique_immediate_of_place O hb hx'
    subst x
    simp [Concurrent];
    intro dup
    obtain ⟨ha', _⟩ := (mem_sub_of_nodup dup).mp ha
    cases hx with
    | single i => obtain := mem_pre_of_lt i; contradiction
    | @tail x _ _ hx =>
      obtain  ⟨c, _, hc⟩ := exists_eq_inl_of_lt_inr hx
      obtain hc' : c ∈ m := mem_of_le en hc
      have ne : a ≠ c := by by_contra h; simp_all only [not_true_eq_false]
      exists a, ha', c
      simp [hc', ne, concurrent, ne_comm]
      subst x
      intros; simp_all
      contradiction

lemma no_concurrent_of_depends_on_post (en : •⦃N⦄t ≤ m) (ha : a ∈ m - •⦃N⦄t) (hb : b ∈ t•⦃N⦄)
    (h : inl b ≼⦃N⦄ inl a) : ¬ Concurrent N m := by
  unfold Concurrent concurrent
  intro ⟨dup, C⟩
  obtain ⟨c, cin⟩ := exists_mem_of_ne_zero (N.cons_prod t).left
  obtain hc : c ∈ m := mem_of_le en cin
  obtain heq : ¬ c = a := fun h => ((mem_sub_of_nodup dup).mp ha).right (h ▸ cin)
  specialize C (mem_of_le (Multiset.sub_le_self m (•⦃N⦄ t)) ha) hc (ne_comm.1 heq)
  obtain : inl c ≼⦃N⦄ inl a := .trans (preorder_of_mem_pre_mem_post cin hb) h
  simp_all

lemma no_concurrent_of_contains_conflicting_cause (en : •⦃N⦄t ≤ m) (ha : a ∈ m - •⦃N⦄t)
    (h : inr t' ≺⦃N⦄ inl a) (c : t' #₀⦃N⦄ t) : ¬ Concurrent N m := by
  simp [immediate_conflict, Disjoint, Multiset.le_zero] at c
  obtain ⟨_, _, le, le', ne⟩ := c
  obtain ⟨b, hb⟩ := exists_mem_of_ne_zero ne
  obtain hb' : b ∈  •⦃N⦄ t := by exact mem_of_le le' hb
  have : inl b ≼⦃N⦄ inl a :=
    .trans (preorder_of_mem_pre (mem_of_le le hb)) (preorder_of_causal h)
  simp_all [Concurrent]
  intro dup
  obtain ⟨ha', ha''⟩ := (mem_sub_of_nodup dup).mp ha
  exists b, (mem_of_le en hb'), a , ha', (fun h => ha'' (h ▸ hb'))
  simp_all [concurrent]

lemma no_concurrent_of_conflicting_causes (en : •⦃N⦄t ≤ m) (ha : a ∈ m - •⦃N⦄t)
    (h : inr t' ≺⦃N⦄ inl a) (h' : inr t'' ≺⦃N⦄ inr t) (c : t' #₀⦃N⦄ t'') :
    ¬ Concurrent N m  := by
  simp [Disjoint, immediate_conflict] at c;
  obtain ⟨ne, _, h1, h2, nz⟩ := c
  cases h' with
  | single h  => simp [immediate] at h
  | @tail x _ _ hx =>
    by_contra C; obtain ⟨nodup, cc⟩ := C
    obtain ⟨ha, ha'⟩ := (mem_sub_of_nodup nodup).mp ha
    obtain ⟨c, _, hc⟩ := exists_eq_inl_of_lt_inr hx; subst x
    have hco := cc ha (mem_of_le en hc) (ne_comm.mp (fun h => ha' (h ▸ hc)))
    obtain ⟨_,x2⟩ := exists_mem_of_ne_zero (by rw [le_zero] at nz; exact nz)
    obtain : t' #₀⦃N⦄ t'' := immediate_conflict_of_shared_place ne (mem_of_le h1 x2)
                (mem_of_le h2 x2)
    contrapose! hco; simp [concurrent]
    intros; simp [conflict, immediate_conflict]
    exists t', h, t''

lemma no_conflict_of_concurrent_preset_postset (O : is_occurrence N) (e : •⦃N⦄t ≤ m)
    (ha : a ∈ m - •⦃N⦄t) (hb : b ∈ t•⦃N⦄) (cf : inl a #⦃N⦄ inl b) : ¬ Concurrent N m := by
  contrapose! cf;
  simp only [conflict, exists_and_left, not_exists, not_and]
  intro _ ha' d t₂Fb
  simp at ha'; contrapose! cf;
  cases t₂Fb with
  | @tail c c' dFc cFb  =>
    have : c = inr t := unique_immediate_of_place O hb cFb; subst c
    cases dFc with
    | refl =>
      exact no_concurrent_of_contains_conflicting_cause e ha ha' cf
    | tail dFb bFt =>  exact
      no_concurrent_of_conflicting_causes e ha ha' (causal_of_preorder_and_lt dFb bFt) cf

lemma in_conc_postset_concurrent (O : is_occurrence N) (C : Concurrent N m) (e : •⦃N⦄t ≤ m)
    (ne : a ≠ b) (ha : a ∈ m - •⦃N⦄t) (hb : b ∈ t•⦃N⦄) :  inl b co⦃N⦄ inl a := by
  simp_all [ne_comm, concurrent]
  repeat' constructor
  · contrapose! C; exact no_concurrent_of_depends_on_post e ha hb (preorder_of_causal C)
  · contrapose! C; exact no_concurrent_of_contains_cause_post O e ha hb C
  · contrapose! C; exact no_conflict_of_concurrent_preset_postset O e ha hb (conflict_symm C)

section
omit [DecidableEq α]
lemma conc_mem_pre_of_conc_post (ha : a ∈ •⦃N⦄t) (hb : b ∈ t•⦃N⦄)
    (h : x co⦃N⦄ inl b) (h' : ¬inl a ≼⦃N⦄ x) :  x co⦃N⦄ inl a := by
  have c :=  preorder_of_causal <| causal_of_mem_pre_mem_post ha hb
  unfold concurrent at *;
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, h', ?_⟩
  · rintro rfl
    contradiction
  · intro h
    exact absurd (ReflTransGen.trans h c) h2
  · unfold conflict at *; contrapose! h4
    obtain ⟨t', t'', ht', ht'', ic⟩ := h4
    exists t', t''
    exact ⟨ht', ReflTransGen.trans ht'' c, ic⟩
end

section
omit [DecidableEq α]
lemma not_refl_of_not_trans {r} (h2 : x ≠ y) (h1 : ¬ TransGen r x y) :
  ¬ ReflTransGen r x y := by
  rw [reflTransGen_iff_eq_or_transGen]
  simp_all [ne_comm]

lemma ne_mem_pre_of_concurrent_mem_post (C : Concurrent N ({a} + t•⦃N⦄)) (h : b ∈ •⦃N⦄t) :
    b ≠ a := by
  obtain ⟨c, hc⟩ := exists_mem_of_ne_zero (N.cons_prod t).2
  obtain ne : a ≠ c := fun h_eq => C.left.notMem (h_eq ▸ hc)
  rintro rfl
  have np := C.right (mem_cons_self b (t•⦃N⦄)) (mem_of_le (le_add_left (t•⦃N⦄) {b}) hc) ne
  exact absurd (preorder_of_mem_pre_mem_post h hc) np.2.1

lemma not_causal_mem_pre_of_concurrent_postset (C : Concurrent N ({a} + t•⦃N⦄))
    (hb : b ∈ •⦃N⦄t) : ¬ (inl a ≼⦃N⦄ inl b) := by
  intro h
  obtain ⟨c, hc⟩ := exists_mem_of_ne_zero (N.cons_prod t).2
  obtain ne : a ≠ c := fun h_eq => C.left.notMem (h_eq ▸ hc)
  obtain  H := C.right (mem_cons_self a (t•⦃N⦄))
            (mem_of_le (le_add_left (t•⦃N⦄) {a} ) hc) ne
  exact absurd (.trans h (preorder_of_mem_pre_mem_post hb hc)) H.2.1

lemma not_preorder_of_cause_of_concurrent_cause (C : Concurrent N ({a} + postsetₜ N t))
    (hb : b ∈ presetₜ N t) (ic : immediate N (inl b) x) : ¬ x ≼⦃N⦄ inl a := by
  obtain ⟨t', rfl⟩ := exists_eq_inr_of_gt_inr ic
  intro cs
  by_cases eq : (t = t')
  · subst t'
    rcases cs.cases_head with (cs | cs)
    · simp_all only [singleton_add, reduceCtorEq]
    · obtain ⟨_, i, hi⟩ := cs
      obtain ⟨d, rfl⟩ := exists_eq_inl_of_gt_inr i
      obtain ne : a ≠ d :=  fun h_eq =>
          (disjoint_left.mp (disjoint_of_nodup_add C.left) <| mem_cons_self a {})
          (h_eq ▸ (mem_post_of_lt i))
      obtain hd := mem_of_le (le_add_left t•⦃N⦄ {a}) (mem_post_of_lt i)
      obtain H  := C.right (mem_cons_self a (t•⦃N⦄)) hd ne
      exact absurd hi H.2.2.1
  · obtain ic := immediate_conflict_of_shared_place eq  (mem_pre_of_lt hb) (mem_pre_of_lt ic)
    obtain ⟨c, hc⟩ := exists_mem_of_ne_zero (N.cons_prod t).2
    obtain ne : a ≠ c := fun h_eq => C.left.notMem (h_eq ▸ hc)
    obtain cf := conflict_inherits_left
                (conflict_inherits_right (conflict_of_immediate_conflict ic) cs)
                (preorder_of_mem_pos hc)
    have H := C.right (Multiset.mem_of_le (le_add_left (t•⦃N⦄) {a}) hc)
                (Multiset.mem_cons_self a (t•⦃N⦄)) (ne_comm.mp ne)
    exact absurd cf H.2.2.2

lemma not_causal_concurrent_postset_of_mem_pre (C : Concurrent N ({a} + t•⦃N⦄))
    (hb : b ∈ •⦃N⦄t) : ¬ (inl b ≼⦃N⦄ inl a) := by
  intro h
  rcases h.cases_head with (h | h)
  · have := ne_mem_pre_of_concurrent_mem_post C hb
    simp_all only [singleton_add, preorder_iff_eq_or_causal, true_or, inl.injEq]
  · obtain ⟨_, ic, cs⟩ := h
    exact absurd cs (not_preorder_of_cause_of_concurrent_cause C hb ic)

lemma conc_mem_pre_if_conc_mem_post (C : Concurrent N ({a} + t•⦃N⦄))
    (h : b ∈ •⦃N⦄t) : inl a co⦃N⦄ inl b := by
  refine⟨?_, ?_, ?_, ?_⟩
  · have ne' : b ≠ a := ne_mem_pre_of_concurrent_mem_post C h
    simp_all [ne_comm]
  · exact not_causal_mem_pre_of_concurrent_postset C h
  · exact not_causal_concurrent_postset_of_mem_pre C h
  · obtain ⟨c, hc⟩ := exists_mem_of_ne_zero (N.cons_prod t).2
    obtain ne : a ≠ c := fun h_eq => C.left.notMem (h_eq ▸ hc)
    intro h
    obtain ⟨t', t'', t'a, t''a, ic⟩ := h
    obtain hh := conflict_inherits_right
      (conflict_inherits_right
        (conflict_inherits_left (conflict_of_immediate_conflict ic) t'a)
          t''a)
      (preorder_of_mem_pre_mem_post h hc)
    obtain := C.right (mem_cons_self a (t•⦃N⦄))
              (mem_of_le (le_add_left (t•⦃N⦄) {a}) hc) ne
    unfold concurrent at *
    simp_all

lemma disjoint_add_pre_of_conc_add_post (C : Concurrent N (m + t•⦃N⦄)) :
    Disjoint m  (•⦃N⦄t) := by
  have ⟨nd, c⟩ := C
  obtain ⟨ndm, _, neq⟩ := nodup_add.mp nd
  rw [disjoint_iff_ne] at *
  contrapose! c
  obtain ⟨y, hy⟩ := exists_mem_of_ne_zero (N.cons_prod t).right
  obtain ⟨x , hx , z , hz, eq⟩ := c
  subst eq
  specialize neq x hx y hy
  exists x, y, mem_of_le (le_add_right m (N.post t)) hx,
    mem_of_le (le_add_left (N.post t) m) hy, neq
  simp[concurrent]
  intros
  have := causal_of_mem_pre_mem_post hz hy
  contradiction

lemma nodup_add_pre_of_conc_add_post (O : is_occurrence N) (C : Concurrent N (m + t•⦃N⦄)) :
    Nodup (m + •⦃N⦄t) := by
    obtain ⟨ndm, ndp, _⟩  := nodup_add.mp C.left
    exact nodup_add.mpr  ⟨ndm, O.set_preset t, disjoint_add_pre_of_conc_add_post C⟩

lemma concurrent_of_le [DecidableEq α] (C : Concurrent N m) (h : m' ≤ m) : Concurrent N m'  := by
  obtain ⟨nd, c⟩ := C
  constructor
  · exact nodup_of_le h nd
  · intro x y hx hy en
    exact c (mem_of_le h hx) (mem_of_le h hy) en

lemma conc_pre_of_conc_post [DecidableEq α] (O : is_occurrence N) (C : Concurrent N (m + t•⦃N⦄)) :
    Concurrent N (m +  •⦃N⦄t) := by
  have ⟨nd, c⟩ := C
  obtain ⟨ndm, _, neq⟩ := nodup_add.mp nd
  constructor
  · exact nodup_add_pre_of_conc_add_post O C
  · contrapose! c
    obtain ⟨x , y, hx , hy, neq, nc⟩ := c
    rcases (mem_add.mp hx) with (hx | hx)
    · rcases (mem_add.mp hy) with (hy | hy)
      · exists x, y
        simp_all only [mem_add, true_or, ne_eq, not_false_eq_true, and_self]
      · have le : ({x} + t•⦃N⦄)  ≤ m + t•⦃N⦄ := le_of_mem hx (t•⦃N⦄)
        exact absurd (conc_mem_pre_if_conc_mem_post (concurrent_of_le C le) hy) nc
    · rcases (Multiset.mem_add.mp hy) with (hy | hy)
      · have le : ({y} + t•⦃N⦄)  ≤ m + t•⦃N⦄ := le_of_mem hy (t•⦃N⦄)
        have pre := (concurrent_of_le C le)
        have := conc_mem_pre_if_conc_mem_post pre hx
        simp_all [co_symm]
      · exact absurd (concurrent_from_same_preset O neq hx hy) nc
end

lemma firing_preserves_concurrent (O : is_occurrence N) (C : Concurrent N m) {e : •⦃N⦄t ≤ m}
    (h : m 〚e⟩⦃N⦄ m') (ha : a ∈ m') (hb : b ∈ m') (ne : a ≠ b) : inl a co⦃N⦄ inl b := by
  unfold is_firing marking_after_firing at h; subst m'
  rcases mem_add.mp ha with ha' | ha''
  · cases mem_add.mp hb with
    | inl hb' =>
      obtain ⟨a1a, _⟩ := (mem_sub_of_nodup C.left).mp ha'
      obtain ⟨b1a, _⟩ := (mem_sub_of_nodup C.left).mp hb'
      exact C.right a1a b1a ne
    | inr hb'' =>
      obtain ⟨a1a, a1b⟩ := (mem_sub_of_nodup C.left).mp ha'
      unfold concurrent; simp_all [ne_eq, inl.injEq, ne_comm]
      repeat' (constructor ; contrapose! C)
      ·  exact no_concurrent_of_contains_cause_post O e ha' hb'' C
      ·  exact no_concurrent_of_depends_on_post e ha' hb'' (preorder_of_causal C)
      ·  contrapose! C; exact no_conflict_of_concurrent_preset_postset O e ha' hb'' C
  · cases mem_add.mp hb with
    | inl hb' => exact in_conc_postset_concurrent O C e (ne_comm.mp ne) hb' ha''
    | inr hb'' => exact concurrent_from_same_postset O ne ha'' hb''

lemma firing_preserves_concurrency (O : is_occurrence N) (C : Concurrent N m) {e : m 〚t〛⦃N⦄}
    (h : m 〚e⟩⦃N⦄ m') : Concurrent N m' := by
  unfold Concurrent ; unfold is_enabled at e;
  constructor
  · subst m'; simp [nodup_add]
    obtain d := disjoint_of_subset_left (subset_of_le (Multiset.sub_le_self m (•⦃N⦄ t)))
      (post_disjoint_of_contains_pre O C e)
    exact ⟨Multiset.nodup_of_le (Multiset.sub_le_self m (•⦃N⦄ t)) C.left, O.set_postset t, d⟩
  · exact firing_preserves_concurrent O C h

lemma firing_sequence_preserves_concurrent
    (O : is_occurrence N) (ts : List β) (C : Concurrent N m) (f : m 〚ts⟩⟩⦃N⦄ m') :
    Concurrent N m' := by
  induction ts generalizing m with
  | nil  =>  obtain :=  target_of_empty_fs f; subst m'; exact C
  | cons hd tl ih =>
    cases f with
    | step _ f fs'=> exact ih (firing_preserves_concurrency O C f) fs'

variable {M : MarkedNet α β}

omit [DecidableEq α] in
lemma minimal_places_concurrent (MO : is_marked_occurrence M) : Concurrent M.toNet M.m₀ := by
  constructor
  · exact MO.initial_set
  · intro a b ha hb ne
    have ne : (inl (β := β) a) ≠ (inl  b) := by simp_all [inl.injEq]
    obtain := not_cause_of_minimal (MO.inital_minimal ha) (ne_comm.mp ne)
    obtain := not_cause_of_minimal (MO.inital_minimal hb)  ne
    simp_all [concurrent, conflict]
    intros c
    have : ¬ inr c = inl a → ¬ inr c ≼⦃M⦄ inl a := by
      exact not_cause_of_minimal (MO.inital_minimal ha)
    simp_all

theorem occ_net_safe (MO : is_marked_occurrence M) : safe M := by
  simp [safe, reachable, is_reachable]
  intro m ts fs
  exact firing_sequence_preserves_concurrent MO.occurrence ts
            (minimal_places_concurrent MO) fs |>.left

end OccurrenceNet
