import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
open Multiset

/-!
# Basic definitions of Petri Net

A `Net` is a structure that is build from two types: `α` for places and `β` for transitions.
N = (α, β, pre, post) is a place/transition Petri net (or only 'net') and (N,m₀) is a marked
net, where m₀ is the initial multiset.

## Main definitions

 Notation used here:
 For a Petri net `N : Net α β`,
  * Enabled transition: A transition `t` enabled in a multiset `m` is written by `m〚t〛⦃N⦄`
    [〚 using `\llb`, 〛using `\rrb`, ⦃⦄ using `\{{}}` or `\{{` `\}}`]
  * Execution (firing): Given a multiset `m₁` and a transition `t`, returns the multiset
  `m₂`. If `m₁ ⟦en⟩⦃N⦄ = m₂` is true, we can denote as `m₁〚en⟩⦃N⦄ m₂`, where `en : (m₁〚t〛⦃N⦄)`.
    [⟩ using `\ran` .. `\rangle`]
  * `m₁〚ts⟩⟩⦃N⦄ m₂ : Prop` is an abreviature if there are sequences of multisets `m₀,m₁,...,mₙ`
  and a list of transitions `ts = [t₁,t₂,...,tₙ]` which `mᵢ₋₁〚enᵢ⟩⦃N⦄ mᵢ` for each i = 1,...,n.

## Standard variable for types
  * `N : Net α β`
  * `M : MarkedNet α β`

-/

universe u v
variable {α : Type} [DecidableEq α] {β : Type}

namespace Nets

/-- A **net** is a structure with places `α`, transitions `β`, functions `pre`, `post`
and the condition `∀ t , pre t ≠ ∅ ∧ post t ≠ ∅`.
-/

@[ext]
structure Net (α : Type) (β : Type) where
  pre : β → Multiset α
  post : β → Multiset α
  cons_prod : (∀ t , pre t ≠ ∅ ∧ post t ≠ ∅)

section ExampleNetN₁
inductive Tr | t₁ | t₂
open Tr


inductive Pl | a | b | c | d | e
deriving  DecidableEq

open Pl

def pre : Tr →  Multiset Pl
    | t₁ => {a, b}
    | t₂ => {b, c}

def post : Tr →  Multiset Pl
    | t₁ => {d}
    | t₂ => {e}

def cons_prod : ∀ t : Tr, pre t ≠ ∅ ∧ post t ≠ ∅ :=  by
  intro t
  cases h: t; all_goals {unfold pre post; simp_all}

#check ({pre := pre, post := post, cons_prod := cons_prod} : Net Pl Tr)

def N₁ : Net Pl Tr :=  ⟨pre, post, cons_prod⟩
end ExampleNetN₁


@[reducible] def presetₚ (N : Net α β) (p : α) : Set β :=
  {t | p ∈ N.post t}

@[reducible, simp] def presetₜ (N : Net α β) (t : β) : Multiset α :=
  N.pre t

notation:max "•⦃" N "⦄" p:max => presetₚ ↑N p
notation:max "•⦃" N "⦄" t:max => presetₜ ↑N t

@[reducible] def postsetₚ (N : Net α β) (p : α) : Set β :=
  {t | p ∈ •⦃N⦄ t}

@[reducible, simp] def postsetₜ (N : Net α β) (t : β) : Multiset α :=
  N.post t

notation:max p:max "•⦃" N "⦄" => postsetₚ ↑N p
notation:max t:max "•⦃" N "⦄" => postsetₜ ↑N t

open Pl Tr

example : presetₚ N₁ a = ∅ := by
  apply Set.ext
  intro t
  unfold presetₚ Net.post N₁ post
  constructor
  · cases t; all_goals{intro ain; simp_all}
  · simp

example : presetₚ N₁ d = {t₁} := by
  apply Set.ext
  intro t
  unfold presetₚ Net.post N₁ post
  constructor
  · cases t; all_goals {simp}
  · intro; subst t; simp

/-Next definitions say if the multiset doesn't have any transition before (is_initial) or
after (is_final)
-/
def minimal (N : Net α β) : Set α :=
  {p | •⦃N⦄ p = ∅ }

def is_initial (N : Net α β) (s : Set α) : Prop :=
  s ⊆ minimal N

example : is_initial (N:= N₁) {a, b, c} := by
  unfold is_initial minimal presetₚ
  intro x p
  apply Set.ext
  intro t
  rcases p with h1 | h2 | h3
  all_goals{
    cases t
    constructor
    repeat' all_goals{ unfold Net.post N₁ post; simp_all}
    }

def maximal (N : Net α β) : Set α :=
  {p | p•⦃N⦄ = ∅ }

def is_maximal (N : Net α β) (s : Set α) : Prop :=
  s ⊆ maximal N

example : is_maximal N₁ {d,e} := by
  unfold is_maximal maximal postsetₚ
  intro _ p
  apply Set.ext
  intro t
  rcases p
  all_goals {cases t; all_goals{unfold presetₜ N₁ pre; simp_all}}

/-- **Enabled transitions**

Given a multiset `m`, `enable m` returns the set of transitions that are enabled at `m`.
-/
def is_enabled (N : Net α β) (m : Multiset α) (t : β) : Prop := •⦃N⦄ t ≤ m

notation:50  m:51 " 〚" t:51 "〛⦃" N "⦄" => is_enabled ↑N m t

def enabled (N : Net α β) (m : Multiset α) : Set β :=
   {t | m〚t〛⦃N⦄}

example : enabled  N₁ {a,b,c} = {t₁, t₂} := by
  unfold enabled is_enabled presetₜ Net.pre N₁ pre
  apply Set.ext
  intro t
  cases t
  · simp [cons_le_cons a (singleton_le.mpr (mem_cons_self b {c}))]
  · simp_all [Decidable.le_iff_eq_or_lt, lt_cons_self (b ::ₘ {c}) a]

variable {N : Net α β}
variable {m m' m'' m₀ : Multiset α} {t t' : β} {ts ts₁ ts₂ : List β} {e : m 〚t〛⦃N⦄}

def is_enabled_from (e : (•⦃N⦄t) ≤ m) : m〚t〛⦃N⦄ := e

/-- **Deadlock**
A deadlock is a marking from which no transition can be fired.
-/

def deadlock (N : Net α β) (m : Multiset α) : Prop := IsEmpty (enabled N m)

/-- Firing -/
@[reducible, simp]
def marking_after_firing (N : Net α β) (m : Multiset α) (_ : m 〚t〛⦃N⦄) : Multiset α :=
 m - •⦃N⦄ t + t•⦃N⦄

--Example enabled
def t₁_enabled : {a, b, c}〚t₁〛⦃N₁⦄ := by
  unfold is_enabled presetₜ Net.pre N₁ pre; simp [cons_le_cons]

def t₂_enabled : {a, b, c}〚t₂〛⦃N₁⦄ := by
  unfold is_enabled presetₜ Net.pre N₁ pre
  rw [Decidable.le_iff_lt_or_eq]
  left
  exact Multiset.lt_cons_self (b ::ₘ {c}) a

example : marking_after_firing N₁ {a, b, c} t₁_enabled  = {c, d} := by
  unfold marking_after_firing presetₜ postsetₜ Net.pre Net.post N₁ pre post; simp only
  simp

def is_firing (N : Net α β) (m : Multiset α) (h : m 〚t〛⦃N⦄) (m' : Multiset α) : Prop :=
  marking_after_firing N m h = m'

lemma is_firing_of_enabled (e : m 〚t〛⦃N⦄) : is_firing N m e (m - •⦃N⦄ t +  t•⦃N⦄) := by
  unfold is_firing marking_after_firing; simp

notation:50  m:50 " 〚" h:51 "⟩⦃" N "⦄ " q:51 => is_firing ↑N m h q

example : {a,b,c} 〚t₁_enabled⟩⦃N₁⦄ {d,c} := by
  unfold N₁ is_firing t₁_enabled marking_after_firing presetₜ postsetₜ Net.pre Net.post pre post
  simp
  rw [←singleton_add, ←singleton_add, Multiset.add_comm]

/-- **Firing sequence**

`firing_sequence N m ls m'` is the concatenation of sequences, where `ls` is the sequence
of transitions, `m` is the initial marking and `m'` the final marking of the sequence.
-/

inductive firing_sequence : Net α β → Multiset α → List β → Multiset α → Prop
| empty m :
    firing_sequence _ m [] m
| step {N : Net α β} {t} {ts} {m m' m''}
    (et : m 〚t〛⦃N⦄)
    (f : m 〚et⟩⦃N⦄  m')
    (fs : firing_sequence N m' ts m'') :
    firing_sequence N m (t :: ts) m''

@[simp] def is_firing_sequence (N : Net α β) (m : Multiset α) (ts : List β) (m' : Multiset α) :=
  firing_sequence N m ts m'

notation:50  m:50 " 〚" h:0 "⟩⟩⦃" N "⦄ " q:51 => is_firing_sequence ↑N m h q

section NetN₂
/--
Applying firing sequence to the net N₁ is not interesting,
because all its secuences have at most length one.
So, let’s considering the net N₂.
-/
inductive Tr₂ | r₁ | r₂ | r₃ | r₄
open Tr₂

def pre2 : Tr₂ →  Multiset ℕ
    | r₁ => {1}
    | r₂ => {2}
    | r₃ => {3,4}
    | r₄ => {4,5}

def post2 : Tr₂ →  Multiset ℕ
    | r₁ => {4}
    | r₂ => {5}
    | r₃ => {6}
    | r₄ => {7}

def cons_prod2 : ∀ t : Tr₂, pre2 t ≠ ∅ ∧ post2 t ≠ ∅ :=  by
  intro t
  cases h: t; all_goals {unfold pre2 post2; simp_all}

def N₂ : Net ℕ Tr₂ :=  ⟨pre2, post2, cons_prod2⟩


example : {1, 2, 3} 〚[r₁, r₂, r₃]⟩⟩⦃N₂⦄ {5, 6} := by
  unfold is_firing_sequence
  obtain et₁ : {1, 2, 3} 〚r₁〛⦃N₂⦄:= by unfold is_enabled presetₜ N₂ Net.pre pre2; simp
  obtain fir₁ : {1, 2, 3} 〚et₁⟩⦃N₂⦄ {4, 2, 3} := Multiset.add_comm ({2} + {3}) {4}
  obtain et₂ : {4,2,3} 〚r₂〛⦃N₂⦄:= by unfold is_enabled N₂ presetₜ pre2; simp
  obtain fir₂ : {4,2,3} 〚et₂⟩⦃N₂⦄ {4,5,3} := by
    unfold is_firing marking_after_firing N₂ postsetₜ post2 pre2
    simp
    exact pair_comm 3 5
  obtain et₃ : {4,5,3}〚r₃〛⦃N₂⦄ := by
    unfold is_enabled N₂ post2 pre2
    rw [le_iff_exists_add]
    exists {5}
  obtain fir₃ : {4,5,3}〚et₃⟩⦃N₂⦄ {5,6} := by
    unfold is_firing marking_after_firing N₂ pre2 post2; simp
  apply firing_sequence.step et₁ fir₁ <|
        .step et₂ fir₂ <|
        .step et₃ fir₃ <|
        .empty {5,6}

end NetN₂

example : {a,b} 〚[t₁]⟩⟩⦃N₁⦄ {d} := by
  have et : {a,b} 〚t₁〛⦃N₁⦄ := by
    unfold is_enabled N₁ pre; simp
  have fir : {a,b} 〚et ⟩⦃N₁⦄ {d} := rfl
  apply firing_sequence.step et fir (firing_sequence.empty {d})

lemma firing_deterministic (ft : m 〚e⟩⦃N⦄ m') (ft' : m 〚e⟩⦃N⦄ m'') : m' = m'' :=
  by unfold is_firing at * ; rw [← ft,← ft']

lemma target_of_empty_fs (fs : m 〚[]⟩⟩⦃N⦄ m') : m' = m :=
  by rcases fs; rfl

lemma tail_of_fs (fs : m 〚t :: ts⟩⟩⦃N⦄ m') : ∃ m'', m'' 〚ts⟩⟩⦃N⦄ m' := by
  cases fs with
  | @step _ _ _ m'' _ _ _ fs => exact ⟨m'', fs⟩

lemma head_of_fs (fs : m 〚t :: ts⟩⟩⦃N⦄ m') :
∃ (e : m 〚t〛⦃N⦄) (m'' : Multiset α), m〚e⟩⦃N⦄ m'' := by
  cases fs with
  | @step _ _ _ m'' _ e fs => exact ⟨e, m'', fs⟩

lemma concat_fs (h1 : m 〚ts₁⟩⟩⦃N⦄ m') (h2 : m' 〚ts₂⟩⟩⦃N⦄ m'') : m 〚ts₁ ++ ts₂⟩⟩⦃N⦄ m'' := by
  induction h1 with
  | empty  =>  simp; exact h2
  | step et ft _ IH => exact (.step et ft (IH h2))

lemma append_split_of_fs (fs : m 〚ts₁ ++ ts₂⟩⟩⦃N⦄ m') :
    ∃ m'', m〚ts₁⟩⟩⦃N⦄ m'' ∧ m''〚ts₂⟩⟩⦃N⦄ m' :=
  by induction ts₁ generalizing m with
  | nil  =>
    exists m; simp_all
    exact .empty m
  | cons hd tl ih =>
    cases fs with
    | step e₀ ft fs' =>
      rcases ih fs' with ⟨m'', ⟨fs₁, fs₂⟩ ⟩
      exists m''
      exact ⟨.step e₀ ft fs₁, fs₂⟩

lemma fs_deterministic (fs : m 〚ts⟩⟩⦃N⦄ m') (fs' : m 〚ts⟩⟩⦃N⦄ m'') : m' = m'' := by
  induction fs with
  | empty m => simp_all [target_of_empty_fs fs']
  | step _ f _  =>
    cases fs' with
    | step  _ f' _ => simp_all [firing_deterministic f f']

lemma non_disjoint_pre_post_if_enabled_after (noe : ¬m〚t'〛⦃N⦄) (fs : m 〚[t, t']⟩⟩⦃N⦄ m') :
    ¬ Disjoint (t•⦃N⦄) (•⦃N⦄ t') := by
  obtain _ |⟨_ , f, _ | ⟨e', f', _⟩ ⟩ := fs
  simp [is_enabled, le_iff_count] at noe e'
  obtain ⟨a, c⟩ := noe
  contrapose! e'
  exists a
  obtain : a ∉ (t •⦃N⦄) := (disjoint_right.mp e') (count_pos.mp (lt_of_le_of_lt (Nat.zero_le _) c))
  subst f;
  simp_all
  exact lt_of_le_of_lt (Nat.sub_le _ _) c

lemma can_swap_if_disjoint_pre_post (fs : m 〚[t, t']⟩⟩⦃N⦄ m') (d : Disjoint (t•⦃N⦄) (•⦃N⦄t')) :
    m 〚t'〛⦃N⦄ := by
  contrapose! d
  exact non_disjoint_pre_post_if_enabled_after d fs

example : firing_sequence N₁ {a, b, c} [t₁] {c, d} :=  by
  apply firing_sequence.step
  · unfold is_firing
    apply Eq.refl
  · exact firing_sequence.empty {c, d}
  · exact t₁_enabled

-- ### Reachable
def is_reachable (N : Net α β) (m m' : Multiset α) : Prop :=
  ∃ fs : List β, firing_sequence N m fs m'

/-- Multiset `d + c` belongs to the set `reach(N, a + b + c)`:
-/
example : is_reachable N₁ ({a} + {b} + {c}) ({d} + {c}) := by
  exists [t₁]
  have fir : {a, b, c}〚t₁_enabled⟩⦃N₁⦄ {d, c} := pair_comm c d
  apply firing_sequence.step t₁_enabled fir (firing_sequence.empty {d, c})

lemma reach_after_firing_from_reach (r : is_reachable N m₀ m)
    (fs : m 〚e⟩⦃N⦄ m'') : is_reachable N m₀ m'' := by
  obtain ⟨ts , fs'⟩ := r; exists ts ++ [t]
  exact concat_fs fs' (.step e fs (.empty m''))


@[ext, coe]
structure MarkedNet (α : Type) (β : Type) extends Net α β where
  m₀ : Multiset α

instance : Coe (MarkedNet α β) (Net α β) where
  coe M := M.toNet

/-- Given a multiset `m`, `reachable m` return all the multisets that can be executed by sequences
of firing enabled.
-/
def reachable (M : MarkedNet α β) : Set (Multiset α) :=
  {m' | is_reachable M.toNet M.m₀ m'}

notation:50 N:51 " ↝ " m:51  =>  m ∈ (reachable ↑N)

/-- Reachable markings are sets.
-/
def safe (M : MarkedNet α β) : Prop :=
  ∀ m, M ↝ m → Nodup m

section ExampleMarkedNet
open Pl Tr

def M₁ : MarkedNet Pl Tr :=  ⟨N₁, {a,b,c}⟩

def M₂ : MarkedNet ℕ Tr₂ := ⟨N₂, {1,2,3}⟩

end ExampleMarkedNet
end Nets
