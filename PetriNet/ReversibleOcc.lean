import PetriNet.Occurrence
open Nets
open Multiset

variable {α β : Type}

namespace ReversibleNet

/-- `TransitionType` indicates the direction of a transition in a reversible net, which
can be forward or backward in a net.
-/
inductive TransitionType
| fwd : TransitionType
| bwd : TransitionType

open TransitionType

def opposite (tt : TransitionType) : TransitionType :=
  match tt with
  | fwd  => bwd
  | bwd  => fwd

variable {tt tt' : TransitionType}

@[simp] def eq_of_opposite : opposite tt = opposite tt' ↔ tt = tt' := by
  simp [opposite];
  constructor <;> {rcases tt <;> rcases tt' <;> simp_all}

abbrev Transition (β : Type) :=  β × TransitionType

def isFwd (t : Transition β) : Prop := t.snd = fwd

def isBwd (t : Transition β) : Prop := t.snd = bwd

prefix:50 "▷" => isFwd
prefix:50 "◁" => isBwd

variable {t : Transition β}
lemma is_fwd_of_not_bwd (h : ¬◁t) : ▷t := by
  rcases t with ⟨_ , _|_⟩ ; all_goals {simp_all [isFwd, isBwd]}

theorem ne_of_fwd_bwd {t t' : Transition β} (_ : ▷t) (_ : ◁t') : t ≠ t' := by
  intro; simp_all [isFwd, isBwd]

def reverse (t : Transition β) : Transition β :=
  (t.fst, opposite  (t.snd))

prefix:max "↽" => reverse

-- ## All backward and all forward
/-- `all_forward` states that all elements in the list are forward.
-/
def all_forward : (l : List (Transition β)) → Prop
  | []       =>  true
  | (h :: t) => ▷h ∧ all_forward t

/-- `all_backward` states that all elements in the list are backward.
-/
def all_backward : (l : List (Transition β)) → Prop
  | []       =>  true
  | (h :: t) => ◁h ∧ all_backward t

prefix:50 "▷▷" => all_forward
prefix:50 "◁◁" => all_backward

variable {s₁ s₂ : List (Transition β)}

theorem all_bwd_of_append : ◁◁(s₁ ++ s₂) ↔ ◁◁s₁ ∧ ◁◁s₂ := by
  apply Iff.intro
  · intro h
    induction s₁ with
    | nil => exact ⟨rfl, h⟩
    | cons _ _ tl_ih =>
      unfold all_backward at h; simp_all; exact ⟨h.left, tl_ih.left⟩
  · intro h
    induction s₁ with
    | nil => exact h.right
    | cons _ _ tl_ih =>
      specialize tl_ih ⟨h.left.right, h.right⟩; exact ⟨h.left.left, tl_ih⟩

theorem all_fwd_of_append : ▷▷(s₁ ++ s₂) ↔ ▷▷s₁ ∧ ▷▷s₂ := by
  apply Iff.intro
  · intro h
    induction s₁ with
    | nil => exact ⟨rfl, h⟩
    | cons hd tl tl_ih =>
      unfold all_forward at h; simp_all; exact ⟨h.left, tl_ih.left⟩
  · intro h
    induction  s₁  with
    | nil => exact h.right
    | cons hd tl tl_ih =>
      specialize tl_ih ⟨h.left.right, h.right⟩; exact ⟨h.left.left, tl_ih⟩

open Tr
example : ↽(t₁,fwd) = (t₁,bwd) := rfl

theorem rev_congr {t t' : Transition β} : t = t' → ↽t = ↽t' :=
  congrArg reverse

@[simp] theorem reverse_convolutive (t : Transition β) : ↽(↽t) = t := by
  unfold reverse; rcases t with ⟨_, _ | _⟩; all_goals {unfold opposite ; simp_all only}

-- Inverse transitions
def inverse (t t' : Transition β) : Prop :=
  t = ↽t'

infix:50 " ↽⇀ " => inverse

theorem eq_of_reverse {t t' : Transition β} : t = t' ↔ ↽t = ↽t' := by
  simp_all [reverse];
  constructor <;> {intros eq; cases t; cases t'; simp_all}

variable {t t' : Transition β}

theorem ne_fwd_iff_ne_reverse (_ : ▷t) (_ : ▷t') : t ≠ t' ↔ ↽t ≠ ↽t' := by
  simp_all [isFwd, reverse];
  constructor <;> {intros ne _; apply ne; cases t; cases t'; simp_all}

@[simp] lemma isfwd_iff_reverse_isbwd : ▷↽t ↔ ◁t := by
  unfold isFwd isBwd reverse opposite
  cases t.snd <;> simp

@[simp] lemma reverse_isbwd_iff_isfwd : ◁↽t ↔  ▷t := by
  unfold isFwd isBwd reverse opposite
  cases h: t.snd <;> repeat simp

-- Properties about inverse
@[simp] theorem inverse_of_reversing (t : Transition β) :  t ↽⇀ ↽t := by
  unfold inverse
  rw [reverse_convolutive]

theorem inverse_irrefl (t : Transition β) : ¬ t↽⇀t := by
  intro; simp_all [inverse, reverse, opposite]
  obtain ⟨ _ , h⟩ := t
  rcases h <;> simp_all

variable {t t' t'' : Transition β}

@[simp] theorem inverse_symm : t ↽⇀ t' ↔ t' ↽⇀ t := by
  simp_all [inverse, reverse, opposite]
  constructor <;>
  rcases t with ⟨_, _ | _⟩ <;>
  rcases t' with ⟨_, _ | _⟩ <;>
  simp_all

@[simp] theorem inverse_unique : t ↽⇀ t' → t ↽⇀ t'' → t' = t'' := by
  simp_all [inverse, reverse, Prod.eq_iff_fst_eq_snd_eq]

lemma neq_of_not_inverse (_ : ¬t ↽⇀ t') : ¬(↽t = ↽↽t') := by
  simp [reverse_convolutive]; intro h;  subst t'; simp_all

/-- ### Reversible
For each `t, t' ∈  Transition β` then `•t = t'•` if `t` and `t'` are reversing.
-/
@[ext]
structure Reversible (α : Type) (β : Type) extends Net α (Transition β) where
  welldef (t t' : Transition β) : t ↽⇀ t' → •⦃toNet⦄ t = t'•⦃toNet⦄

instance (α β : Type) : Coe (Reversible α β) (Net α (Transition β)) where
  coe r := r.toNet

attribute [coe] Reversible.toNet

@[simp] theorem eq_pre_post_of_inverse (R : Reversible α β) (i : t ↽⇀ t') :
    •⦃R.toNet⦄ t = t'•⦃R.toNet⦄ := by
  exact (R.welldef t t') i

-- The forward subnet consist of the net where only forward transitions are considered
def fwd_subnet (N : Net α (Transition β)) : Net α β :=
  { pre := fun x => N.pre (x, fwd),
    post := fun x => N.post (x, fwd),
    cons_prod := by
      intro t
      apply And.intro
      · exact (N.cons_prod (t,fwd)).left
      · exact (N.cons_prod (t, fwd)).right }

variable {a : α} {t t' : Transition β}
variable {R : Reversible α β}

lemma mem_pre_of_mem_pre (ft : ▷t) (h : a ∈ •⦃R.toNet⦄t) :
    a ∈ •⦃fwd_subnet R.toNet⦄ t.fst  := by
  unfold fwd_subnet isFwd at *
  rcases t with ⟨_, fwd | bwd⟩;  all_goals{simp_all}

lemma mem_post_of_mem_post (ft : ▷t) (h : a ∈ t•⦃R.toNet⦄) :
    a ∈  t.fst•⦃fwd_subnet R.toNet⦄ := by
  unfold fwd_subnet isFwd at *
  rcases t with ⟨_, fwd | bwd⟩;  all_goals{simp_all}

@[simp] theorem mem_pre_fwd_iff_mem_post_bwd (i : t ↽⇀ t') :
    a ∈ •⦃R.toNet⦄ t ↔ a ∈ t' •⦃R.toNet⦄ := by
  exact Eq.to_iff <| congrFun (congrArg Membership.mem <| R.welldef t t' i) a

@[simp] theorem in_post_bwd_iff_in_pre_fwd (i : t ↽⇀ t') :
    a ∈ t •⦃R.toNet⦄ ↔ a ∈ •⦃R.toNet⦄ t' := by
  obtain h1 := R.welldef t' t
  rw [inverse_symm] at h1 ; specialize h1 i ; rw [h1]

@[simp] lemma enabled_rev_iff_enabled_fwd_subnet {m : Multiset α} :
    m〚t.fst〛⦃fwd_subnet R⦄ ↔ m〚(t.fst,fwd)〛⦃R⦄ := by
  unfold is_enabled fwd_subnet at *
  simp_all

@[simp] lemma firing_rev_iff_firing_fwd_subnet [DecidableEq α] {m m' : Multiset α}
    {t : Transition β} {et : m 〚(t.fst, fwd)〛⦃R.toNet⦄} {et' : m 〚t.fst〛⦃fwd_subnet R.toNet⦄} :
    is_firing (fwd_subnet R.toNet) m et m' ↔ is_firing R.toNet m et' m' := by
  unfold is_firing marking_after_firing is_enabled fwd_subnet at *
  simp

variable [DecidableEq α]
variable {m m' : Multiset α}

theorem inverse_enabled_after_firing (e : m 〚t〛⦃R⦄) (f : m 〚e⟩⦃R.toNet⦄ m') :
    ∃ t', t' ↽⇀ t ∧ m'〚t'〛⦃R⦄ := by
  exists (↽t)
  constructor
  · simp [inverse]
  · obtain w := R.welldef (↽t) t
    simp_all [inverse, reverse, is_firing, marking_after_firing, is_enabled]
    subst f
    exact Multiset.le_add_left (R.post t) (m - R.pre t)

lemma cancelation (i : t ↽⇀ t') {e : m 〚t〛⦃R⦄} (f : m 〚e⟩⦃R.toNet⦄ m') (h' : m' 〚t'〛⦃R⦄) :
    m'〚h'⟩⦃R.toNet⦄ m := by
  have rev : t' ↽⇀ t := inverse_symm.mpr i
  unfold is_firing marking_after_firing at *
  subst f
  rw [R.welldef t' t rev, ← R.welldef t t', Multiset.add_comm,
    Multiset.add_sub_cancel_right, submultiset_cancelation e]
  exact i
end ReversibleNet

section ReversibleNetR₁
--Example of the N₁'s reversible net
open Tr Pl ReversibleNet

def pre' : (Transition Tr) →  Multiset Pl
    | (t₁, .fwd) => {a, b}
    | (t₁, .bwd) => {d}
    | (t₂, .fwd) => {b, c}
    | (t₂, .bwd) => {e}

def post' : (Transition Tr) →  Multiset Pl
    | (t₁, .fwd) => {d}
    | (t₁, .bwd) => {a, b}
    | (t₂, .fwd) => {e}
    | (t₂, .bwd) => {b, c}

def cons_prod' : ∀ t : Transition Tr, pre' t ≠ ∅ ∧ post' t ≠ ∅ :=  by
  intro t
  cases t; all_goals {unfold pre' post'; aesop}

def N₁' : Net Pl (Transition Tr) := ⟨pre', post', cons_prod'⟩

def welldef' (t t' : Transition Tr) (h : t ↽⇀ t') : •⦃N₁'⦄ t = t'•⦃N₁'⦄ := by
  unfold inverse reverse opposite at h ; unfold presetₜ postsetₜ Net.pre Net.post
  rcases t with ⟨v, fwd | bwd⟩ ; all_goals {
    rcases t' with ⟨v', fwd | bwd⟩ ; all_goals {
      cases v'; all_goals {unfold N₁' pre' post'; simp_all}
      }
    }

def R₁ : Reversible Pl Tr := ⟨N₁', welldef'⟩
end ReversibleNetR₁

namespace ReversibleOcc
open ReversibleNet ReversibleNet.TransitionType

/-- ## Reversible occurrence
A reversible ocurrence is a reversible and occurrence net.
Given a reversible net `Reversible α β` and a prove of its occurrence, then
we have a reversible occurrence net.
-/

@[ext]
structure ReversibleOccurrence (α : Type) (β : Type) extends Reversible α β where
  isOccurrence : is_occurrence (fwd_subnet toNet)

instance {α β : Type} : Coe (ReversibleOccurrence α β) (Reversible  α β) where
  coe r := r.toReversible

instance {α β : Type} : Coe (ReversibleOccurrence α β) (Net  α (Transition β)) where
  coe r := r.toNet

attribute [coe] ReversibleOccurrence.toReversible

structure MarkedReversibleOccurrence α β extends Reversible α β where
  m₀ : Multiset α
  isFwdMarkedOcurrence : is_marked_occurrence ⟨fwd_subnet toNet, m₀⟩

instance {α β : Type} : Coe (MarkedReversibleOccurrence α β) (Net  α (Transition β)) where
  coe r := r.toNet

attribute [coe] MarkedReversibleOccurrence.toReversible

@[coe] def markedRO_to_markedN (MO : MarkedReversibleOccurrence α β) : MarkedNet α (Transition β) :=
  ⟨MO.toNet, MO.m₀⟩

@[coe] def markedRO_to_RO (MO : MarkedReversibleOccurrence α β) : ReversibleOccurrence α β :=
  ⟨MO.toReversible, MO.isFwdMarkedOcurrence.occurrence⟩

variable {t t' : Transition β} {m₀ m m' : Multiset α}

lemma minus_post_preserves_concurrency_fwd_subnet [DecidableEq α]
    (MO : MarkedReversibleOccurrence α β) (C : Concurrent (fwd_subnet MO.toNet) m)
    (t₁ : β) : Concurrent (fwd_subnet MO.toNet) (m - t₁•⦃fwd_subnet MO.toNet⦄) := by
  unfold Concurrent at *
  constructor
  · exact nodup_sub_of_nodup (t₁•⦃fwd_subnet MO.toNet⦄) C.left
  · intro x y xin zin ne
    have  h1 := mem_of_le (Multiset.sub_le_self m t₁•⦃fwd_subnet MO.toNet⦄) xin
    have  h3 := mem_of_le (Multiset.sub_le_self m t₁•⦃fwd_subnet MO.toNet⦄) zin
    exact C.right h1 h3 ne

lemma minus_post_plus_pre_preserves_concurrency_fwd_subnet [DecidableEq α] {val : β}
    (MO : MarkedReversibleOccurrence α β) (C : Concurrent (fwd_subnet MO.toNet) m)
    (h : val•⦃fwd_subnet MO.toNet⦄ ≤ m) :
    Concurrent (fwd_subnet MO.toNet) (m - val•⦃fwd_subnet MO.toNet⦄ +
    •⦃fwd_subnet MO.toNet⦄ val) := by
  obtain meq := Eq.symm <| Multiset.sub_add_cancel h
  rw [meq] at C
  exact conc_pre_of_conc_post MO.isFwdMarkedOcurrence.occurrence C

lemma firing_preserves_concurrency [DecidableEq α] (MO : MarkedReversibleOccurrence α β)
    (ts : List (Transition β)) (C : Concurrent (fwd_subnet MO.toNet) m) (f : m 〚ts⟩⟩⦃MO.toNet⦄ m') :
    Concurrent (fwd_subnet MO.toNet) m' := by
 induction ts generalizing m with
  | nil  =>  obtain :=  target_of_empty_fs f; subst m'; exact C
  | cons hd tl ih =>
    cases f with
    | @step _ _ _ m'' _ et f fs' =>
      have Occ := MO.isFwdMarkedOcurrence.occurrence
      rcases hd with ⟨val, (fwd | bwd)⟩
      · have et' : m 〚val〛⦃fwd_subnet MO.toNet⦄ := et
        exact ih (firing_preserves_concurrency Occ C (e := et') f) fs'
      · have ht : ⟨val, fwd⟩ ↽⇀ ⟨val, bwd⟩ :=  by simp_all [inverse, reverse, opposite]
        obtain i := MO.welldef (⟨val, bwd⟩) (⟨val, fwd⟩) (inverse_symm.mpr ht)
        obtain i' := MO.welldef (⟨val, fwd⟩) (⟨val, bwd⟩) ht
        have en : m'' = m - (val•⦃fwd_subnet MO.toNet⦄) + (•⦃fwd_subnet MO.toNet⦄ val) := by
            simp_all [inverse, reverse, opposite, is_firing, marking_after_firing, fwd_subnet]
        obtain h1 := le_of_eq_of_le (id (Eq.symm i)) et
        obtain h2 := pre_disjoint_of_contains_post Occ C h1
        have h3 : Disjoint (m - val•⦃fwd_subnet MO.toNet⦄) (•⦃fwd_subnet MO.toNet⦄ val) := by
          have : (m - val•⦃fwd_subnet MO.toNet⦄) ≤ m :=
            Multiset.sub_le_self m (val•⦃fwd_subnet MO.toNet⦄)
          exact disjoint_of_subset_left (subset_of_le this) h2
        obtain C0 := minus_post_preserves_concurrency_fwd_subnet MO C val
        have C' := minus_post_plus_pre_preserves_concurrency_fwd_subnet MO C h1
        rw [←en] at *
        exact ih C' fs'

theorem concurrent_marking_of_reversible_occ_net [DecidableEq α]
    (MO : MarkedReversibleOccurrence α β) (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) :
    Concurrent (fwd_subnet MO.toNet) m := by
  unfold reachable is_reachable at rr
  have ⟨ts, fs⟩ := rr
  simp at fs
  exact firing_preserves_concurrency MO ts (minimal_places_concurrent MO.isFwdMarkedOcurrence) fs

theorem reversible_occ_net_safe [DecidableEq α]
    (MO : MarkedReversibleOccurrence α β) : safe ⟨MO.toNet, MO.m₀⟩ := by
  simp [safe, reachable, is_reachable]
  intro m ts fs
  exact firing_preserves_concurrency MO ts
    (minimal_places_concurrent MO.isFwdMarkedOcurrence) fs |>.left


lemma forward_disjoint_postset (R : ReversibleOccurrence α β)
    (ft : ▷t) (ft' : ▷t') (_ : t ≠ t') : Disjoint (t •⦃R.toNet⦄) (t' •⦃R.toNet⦄) := by
  simp [Disjoint, Multiset.le_zero]
  intros _ h h'
  obtain noback := R.isOccurrence.no_backward_conflict
  contrapose! noback
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero noback
  exists a, t.fst, t'.fst
  rcases t with ⟨_, _ | _⟩
  · rcases t' with ⟨_, _ | _⟩
    · constructor
      · simp_all
      · exact ⟨Multiset.mem_of_le h ha, Multiset.mem_of_le h' ha⟩
    · simp_all [isFwd]
  · simp [isFwd] at ft

lemma backward_disjoint_preset (R : ReversibleOccurrence α β)
    (bt : ◁t) (bt' : ◁t') (ne : t ≠ t') : Disjoint (•⦃R.toNet⦄ t) (•⦃R.toNet⦄ t') := by
  obtain frt := isfwd_iff_reverse_isbwd.mpr bt
  obtain frt' := isfwd_iff_reverse_isbwd.mpr bt'
  have h : (↽t) ≠ (↽t') := by simp_all [ne_fwd_iff_ne_reverse frt frt']
  obtain d := forward_disjoint_postset R frt frt' h
  rw [eq_pre_post_of_inverse R.toReversible (inverse_of_reversing t),
      eq_pre_post_of_inverse R.toReversible (inverse_of_reversing t')]
  exact d

lemma neq_fwd_disjoint_bwd_preset (R : ReversibleOccurrence α β)
    (ft : ▷t) (ft' : ▷t') (ne : t ≠ t') : Disjoint (•⦃R.toNet⦄ ↽t) (•⦃R.toNet⦄ ↽t') := by
  obtain brt : ◁ (↽t) := reverse_isbwd_iff_isfwd.mpr ft
  obtain brt' : ◁ (↽t') := reverse_isbwd_iff_isfwd.mpr ft'
  obtain h : (↽t) ≠ (↽t') := (ne_fwd_iff_ne_reverse ft ft').mp ne
  exact backward_disjoint_preset R brt brt' h

lemma fwd_bwd_disjoint_post_pre (R : ReversibleOccurrence α β)
    (ft : ▷t) (bt' : ◁t') (ne : t ≠ ↽t') : Disjoint (t•⦃R.toNet⦄) (•⦃R.toNet⦄ t') := by
  have frt' : ▷ (↽t') := by simp_all [isfwd_iff_reverse_isbwd]
  rw [R.welldef t' (↽t') (Eq.symm (reverse_convolutive t'))]
  exact forward_disjoint_postset R ft frt' ne

variable {RO : ReversibleOccurrence α β}
variable [DecidableEq α]

lemma loop (i : t ↽⇀ t') :
    (∃ e : m〚t〛⦃RO⦄, m〚e⟩⦃RO.toNet⦄ m') ↔ (∃ e : m'〚t'〛⦃RO⦄, m'〚e⟩⦃RO.toNet⦄ m) := by
  constructor
  · rintro ⟨e, f⟩
    obtain  ⟨rt, i' , e'⟩ := inverse_enabled_after_firing (m' := m') (t := t) e f
    obtain : t' = rt := inverse_unique i (inverse_symm.mpr i')
    subst rt t'
    obtain := cancelation i f e'
    exists e'
  · rintro ⟨e, f⟩
    obtain ⟨rt', i', e'⟩ := inverse_enabled_after_firing (m' := m) (t := t') e f
    rw [← inverse_symm] at i
    obtain : t = rt' := inverse_unique i (inverse_symm.mpr i')
    obtain := cancelation i f
    simp_all

theorem backtracking : (∃ s, m〚s⟩⟩⦃RO.toNet⦄ m') → (∃ s, m'〚s⟩⟩⦃RO.toNet⦄ m) := by
    rintro ⟨s, fs⟩
    induction fs with
    | empty  =>  exists []; exact firing_sequence.empty _
    | @step t _ m m'' _ e f _ ih  =>
      obtain ⟨s, fs⟩ := ih
      obtain i : t ↽⇀ (↽t) := inverse_of_reversing t
      obtain ⟨e, f⟩ := (loop i).mp ⟨e, f⟩
      exact ⟨s ++ [↽t], concat_fs fs (.step e f (.empty m))⟩

end ReversibleOcc
