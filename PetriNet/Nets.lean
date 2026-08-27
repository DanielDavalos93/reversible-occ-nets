module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Rel
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Multiset.Basic
public import PetriNet.MultisetAux
import Architect

open Multiset

@[expose] public section

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

@[blueprint "def:net"
 (title := /-- Net -/)
 (statement := /-- A \emph{net} $N$ is a tuple $N=(\alpha, \beta, \bullet{\_}, \bullet{\_})$,
 where $\alpha$ is a nonempty set of places, $\beta$ is the set of transitions, and
 $•{\_}, {\_}•: \beta →  ℕ ^{\alpha}$ assign source and target to each transition.
We consider only nets in which every transition both consumes and produces, i.e., $•t ≠ ∅$
and $t• ≠ ∅$  for all $t∈ β$. -/),
ext]
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

@[blueprint "def:preset_p"
 (title := /--Preset for places. -/)
 (statement := /-- A \emph{preset for places} is a function that take a net $N$, a place $p$ and
 return the set $\{t \mid p ∈ t•\}$, where the postset function is defined in Definition
 \ref{def:net}. -/)
 (uses := ["def:net"])]
def presetₚ (N : Net α β) (p : α) : Set β :=
  {t | p ∈ N.post t}

@[blueprint "def:preset_t"
 (title := /--Preset for transitions. -/)
 (statement := /-- A \emph{preset for transitions} is a function that take a net $N$, a transition
 $t$ and return the multiset $•t$. -/)
 (uses := ["def:net"]),
 simp]
def presetₜ (N : Net α β) (t : β) : Multiset α :=
  N.pre t

notation:max "•⦃" N "⦄" p:max => presetₚ ↑N p
notation:max "•⦃" N "⦄" t:max => presetₜ ↑N t

@[blueprint "def:postset_p"
 (title := /--Postset for places. -/)
 (statement := /-- A \emph{postset for places} is a function that take a net $N$, a place $p$ and
 return the set $\{t | p ∈ •t \}$, where the preset function is defined in Definition
 \ref{def:net}.
 -/)
 (uses := ["def:net", "def:preset_t"])
 ]
def postsetₚ (N : Net α β) (p : α) : Set β :=
  {t | p ∈ •⦃N⦄ t}

@[blueprint "def:postset_t"
 (title := /--Postset for transitions. -/)
 (statement := /-- A \emph{postset for transitions} is a function that take a net $N$, a transition
 $t$ and return the multiset $t•$.

 The notation for preset of places or transition are written as $\bullet_{ \{\!\{ N \}\!\} }t$, but
 in this file we'll use only the short notation $•t$. -/)
 (uses := ["def:net"]),
 simp]
def postsetₜ (N : Net α β) (t : β) : Multiset α :=
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
@[blueprint "def:minimal"
 (title := /-- Minimal -/)
 (statement := /-- This definition say if the multiset doesn't have any transition before.-/)]
def minimal (N : Net α β) : Set α :=
  {p | •⦃N⦄ p = ∅ }

@[blueprint "def:initial"
 (title := /-- Is minimal -/)
 (statement := /-- A set $s$ is \emph{initial} in a net $N$ if $s ⊆ minimal(N)$. -/)
 (uses := ["def:minimal"])]
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

@[blueprint "def:maximal"
 (title := /-- Maximal -/)
 (statement := /-- This definition say if the multiset doesn't have any transition after.-/)]
def maximal (N : Net α β) : Set α :=
  {p | p•⦃N⦄ = ∅ }

@[blueprint "def:is_maximal"
 (title := /-- Is maximal -/)
 (statement := /-- A set $s$ is \emph{maximal} in a net $N$ if $s ⊆ maximal(N)$. -/)
 (uses := ["def:maximal"])]
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
@[blueprint "def:is_enabled"
 (title := /-- Enabled transition -/)
 (statement := /-- Given a net $N$ and a multiset $m$, a verificator of enabled transition is a
 function $\textsf{is\_enabled}:N → \textsf{Multiset} → β → \textsf{Prop}$ that verifies if 
 $m ≤ •t$. We denote $\textsf{is\_enabled N m t}$ as $m[[t]]_{ \{\!\{ N\}\!\} }$. 
 \footnote{In this documentation we avoid the subscript notation, and instead we write only 
 $m[[t]]$.}-/)
 (uses := ["def:net", "def:preset_t"])]
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
@[blueprint "def:marking_after_firing"
 (statement := /-- Given a net $N$, a transition $t$ and a prove that $t$ is enabled at $m$, 
 the function \textsf{marking\_after\_firing N m e} returns the multiset applied at $m$ on $t$, 
 which is $m - •t + t•$. -/)
 (uses := ["def:is_enabled", "def:postset_t", "def:preset_t"]),
simp]
def marking_after_firing (N : Net α β) (m : Multiset α) (_ : m 〚t〛⦃N⦄) : Multiset α :=
 m - •⦃N⦄ t + t•⦃N⦄

--Example enabled
def t₁_enabled : {a, b, c}〚t₁〛⦃N₁⦄ := by
  unfold is_enabled presetₜ Net.pre N₁ pre; simp

def t₂_enabled : {a, b, c}〚t₂〛⦃N₁⦄ := by
  unfold is_enabled presetₜ Net.pre N₁ pre
  rw [Decidable.le_iff_lt_or_eq]
  left
  exact Multiset.lt_cons_self (b ::ₘ {c}) a

example : marking_after_firing N₁ {a, b, c} t₁_enabled  = {c, d} := by
  unfold marking_after_firing presetₜ postsetₜ Net.pre Net.post N₁ pre post; simp only
  simp

@[blueprint "def:is_firing"
 (title := /-- Firing -/)
 (statement := /-- Given a net $N$, \textsf{is\_firing : N → Multiset $\alpha$ → h → 
 Multiset $\alpha$ → \textsf{Prop}} checks if a firing on a multiset $m$ by $t$ is equal to 
 another multiset $m'$, i.e., if $m[[t⟩ = m'$. We denote this only by $m[[t⟩m'$-/)
 (uses := ["def:is_enabled", "def:marking_after_firing"])]
def is_firing (N : Net α β) (m : Multiset α) (h : m 〚t〛⦃N⦄) (m' : Multiset α) : Prop :=
  marking_after_firing N m h = m'

@[blueprint "lem:is_firing_of_enabled"
 (statement := /-- Let $N$ be a net, $t$ a transition and $m$ a multiset, then 
 $m [[t⟫ (m - •t + t•)$. -/)
 (proof := /-- It is immediate by Definition \ref{def:is_firing} and Definition 
 \ref{def:marking_after_firing}.-/)
 (uses := ["def:is_firing", "def:marking_after_firing"])
 (proofUses := ["def:is_firing", "def:marking_after_firing"])]
lemma is_firing_of_enabled (e : m 〚t〛⦃N⦄) : is_firing N m e (m - •⦃N⦄ t +  t•⦃N⦄) := by
  unfold is_firing marking_after_firing; simp

notation:50  m:50 " 〚" h:51 "⟩⦃" N "⦄ " q:51 => is_firing ↑N m h q

example : {a,b,c} 〚t₁_enabled⟩⦃N₁⦄ {d,c} := by
  unfold N₁ is_firing t₁_enabled marking_after_firing presetₜ postsetₜ Net.pre Net.post pre post
  simp
  rw [←singleton_add, ←singleton_add, Multiset.add_comm]

@[blueprint "def:firing_sequence"
 (title := /-- Firing sequence -/)
 (statement := /-- \texttt{firing\_sequence N m ls m'} is the concatenation of sequences, where 
 $ls$ is the sequence of transitions, $m$ is the initial marking (Definition \ref{def:initial}) 
 and $m'$ the final marking of the sequence. We denote for $s=ε$ for a empty sequence, in Lean 
 this is an empty list, we denote for \textsf{';'} the concatenation of lists. Therefore, a firing 
 sequence is defined inductively as
\begin{itemize}
  \item \textsf{Empty.} $m [[ε⟫ m$
  \item \textsf{Inductive step.} For a sequence $t;s$ where $t$ is a transition and $s$ is a 
  transition sequence, $m[[t;s⟫ m'$ is a firing sequence if there is $m''$ such that $m[[t⟩m''$ is 
  firing and $m''[[s⟫ m'$ is a firing sequence.
\end{itemize}
 -/)
 (uses := ["def:is_enabled", "def:is_firing"])
]
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

@[blueprint "lem:firing_deterministic"
 (title := /-- Firing deterministic -/)
 (statement := /-- For a net $N$ and a transition $t$ enabled at $m$ (where $e$ is a proof that it 
 is enabled), if $m [[t⟩ m'$ and $m [[t⟩ m''$ then $m' = m''$.  -/)
 (uses := ["def:is_firing"])
 (proof := /-- Immediate by unfolding Definition \ref{def:is_firing}. -/)
 (proofUses := ["def:is_firing"])
 (latexEnv := "lemma")]
lemma firing_deterministic (ft : m 〚e⟩⦃N⦄ m') (ft' : m 〚e⟩⦃N⦄ m'') : m' = m'' :=
  by unfold is_firing at * ; rw [← ft,← ft']

@[blueprint "lem:target_of_empty_fs"
 (statement := /-- For every net $N$ and multisets $m,m'$, $m[[ε⟫m'$ implies $m = m'$.  -/)
 (proof := /-- By structural induction on the firing sequence.-/ )
 (proofUses := ["def:firing_sequence"])
 (latexEnv:= "lemma")]
lemma target_of_empty_fs (fs : m 〚[]⟩⟩⦃N⦄ m') : m' = m :=
  by rcases fs; rfl

@[blueprint "lem:tail_of_fs"
 (statement := /-- Let $t$ be a transition and $s$ a sequence (note that $t;s$ is a sequence), 
 $m,m'$ two multisets and $m[[ t;s ⟫ m'$, then there exist a multiset $m''$ such that $m'' [[ s⟫ m$. -/)
 (hasProof := false)
 (proofUses := ["def:firing_sequence"])
 (latexEnv := "lemma")]
lemma tail_of_fs (fs : m 〚t :: ts⟩⟩⦃N⦄ m') : ∃ m'', m'' 〚ts⟩⟩⦃N⦄ m' := by
  cases fs with
  | @step _ _ _ m'' _ _ _ fs => exact ⟨m'', fs⟩

@[blueprint "lem:head_of_fs"
 (statement := /-- Let $t$ be a transition, $s$ a sequence of transitions, $m,m'$ two multisets, 
 and $m[[t;s ⟫ m'$. Then, there exist a multiset $m''$ such that $m[[t⟩ m''$.-/)
 (hasProof := false)
 (latexEnv := "lemma")]
lemma head_of_fs (fs : m 〚t :: ts⟩⟩⦃N⦄ m') :
∃ (e : m 〚t〛⦃N⦄) (m'' : Multiset α), m〚e⟩⦃N⦄ m'' := by
  cases fs with
  | @step _ _ _ m'' _ e fs => exact ⟨e, m'', fs⟩

@[blueprint "lem:concat_fs"
 (title := /-- Concat firing sequence-/)
 (statement := /-- Let be $m[[s_1⟫ m'$ and $m'[[s_2⟫ m''$ two firing sequences. Then $m[[s_1;s_2⟫ m''$.-/)
 (uses := ["def:firing_sequence"])
 (hasProof := false)
 (latexEnv := "lemma")]
lemma concat_fs (h1 : m 〚ts₁⟩⟩⦃N⦄ m') (h2 : m' 〚ts₂⟩⟩⦃N⦄ m'') : m 〚ts₁ ++ ts₂⟩⟩⦃N⦄ m'' := by
  induction h1 with
  | empty  =>  simp; exact h2
  | step et ft _ IH => exact (.step et ft (IH h2))

@[blueprint "lem:append_split_of_fs"
 (title := /-- Append split of firing sequence -/)
 (statement := /-- Let $m[[s_1;s_2⟫ m'$ be a firing sequences, then there is a multiset $m''$ such 
 that $m[[s_1⟫ m''$ and $m''[[s_2⟫ m'$.-/)
 (proof := /-- By induction on the length of $s_1$, and by structural induction on the firing 
 sequence for $s_2$. -/)
 (proofUses := ["def:firing_sequence"])
 (latexEnv := "lemma")]
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

@[blueprint "lem:fs_deterministic"
 (title := /-- Firing sequence deterministic -/)
 (statement := /-- Let be $m [[ s ⟫ m'$ and $m [[ s ⟫ m''$ two firing sequences, then $m' = m''$.-/)
 (hasProof := false)
 (proofUses := ["lem:target_of_empty_fs", "lem:firing_deterministic"])
 (latexEnv := "lemma")]
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


@[ext, coe, blueprint "def:MarkedNet"
 (statement := /-- A \emph{marked net} is a tuple $M = (N,m₀)$, where $N$ is a net (Definition 
 \ref{def:net}) and $m₀$ is the initial marking. -/)
 (uses := ["def:net"])]
structure MarkedNet (α : Type) (β : Type) extends Net α β where
  m₀ : Multiset α

instance : Coe (MarkedNet α β) (Net α β) where
  coe M := M.toNet


@[blueprint "def:reachable"
 (title := /-- Reachable -/)
 (statement := /-- Given a marked net $M$ and a multiset $m$, \emph{reachable N m} return all 
 the multisets that can be executed by sequences of firing enabled.
 We denote a reachable for a marking $m$ of a net $N$ by $N \leadsto m$.-/)
 (uses := ["def:MarkedNet"])
]
def reachable (M : MarkedNet α β) : Set (Multiset α) :=
  {m' | is_reachable M.toNet M.m₀ m'}

notation:50 N:51 " ↝ " m:51  =>  m ∈ (reachable ↑N)

/-- Reachable markings are sets.
-/
@[blueprint "def:safe"
 (title := /-- Safe -/)
 (statement := /-- A marked net $M = (N, m₀)$ is \emph{safe} if for every multiset $m$, $M ↝ m$
 implies that $m$ has no duplicate. -/)
 (uses := ["def:MarkedNet"])]
def safe (M : MarkedNet α β) : Prop :=
  ∀ m, M ↝ m → Nodup m

section ExampleMarkedNet
open Pl Tr

def M₁ : MarkedNet Pl Tr :=  ⟨N₁, {a,b,c}⟩

def M₂ : MarkedNet ℕ Tr₂ := ⟨N₂, {1,2,3}⟩

end ExampleMarkedNet

variable {t₁ t₂ : β} {m1 m2 : Multiset α}

@[blueprint "lem:square"
 (title := /-- Square lemma -/)
 (statement := /-- Let $N$ a net, $m[[t_1⟩m_1$ and $m[[t_2⟩m_2$ two firings, and $•t₁ ∩ •t₂ = ∅ $.
 Then, there is a multiset $m'$ such that $m₁[[t₁⟩m'$ and $m₂ [[t₂⟩ m'$.-/)
 (proof := /-- It is suffices to take $m' = m - •t₁ + t₁• - •t₂ + t₂•$. To prove that $m₁[[t₁]]$ 
 note that we can have $m₁ = m - •t₁ + t₁•$ after firing, and $•t₂ ≤ m - •t₁$. Analousgly with the 
 enabled $m₂[[t₂]]$. -/)
 (uses := ["def:is_enabled", "def:is_firing"])]
lemma square (N : Net α β)
    {e₁ : m 〚t₁〛⦃N⦄} {e₂ : m 〚t₂〛⦃N⦄}
    (_ : m 〚e₁⟩⦃N⦄ m1) (_ : m 〚e₂⟩⦃N⦄ m2)
    (d : Disjoint (•⦃N⦄ t₁) (•⦃N⦄ t₂)) :
  ∃ (e1 : m1 〚t₂〛⦃N⦄), ∃ (e2 : m2 〚t₁〛⦃N⦄), ∃ m', (m1 〚e1⟩⦃N⦄ m' ∧ m2 〚e2⟩⦃N⦄ m') := by
  unfold is_enabled is_firing marking_after_firing at *
  subst m2 m1
  have en1: (•⦃N⦄ t₂) ≤ m - •⦃N⦄ t₁ + t₁•⦃N⦄ := by
    have h_sub : (•⦃N⦄ t₂)  ≤ m - (•⦃N⦄ t₁) := by
      exact disjoint_le_sub e₂ (Disjoint.symm d)
    exact le_trans h_sub (Multiset.le_add_right _ _)
  have en2: (•⦃N⦄ t₁) ≤ m - •⦃N⦄ t₂ + t₂•⦃N⦄ := by
    have h_sub : (•⦃N⦄ t₁)  ≤ m - (•⦃N⦄ t₂) := by
      exact disjoint_le_sub e₁ d
    exact le_trans h_sub (Multiset.le_add_right _ _)
  exists en1, en2, m - •⦃N⦄t₁ + t₁•⦃N⦄ - •⦃N⦄t₂ + t₂•⦃N⦄
  simp
  rw [Multiset.ext, Multiset.le_iff_count] at *
  intro x
  obtain a := Multiset.disjoint_left.mp d
  by_cases h : x ∈ (•⦃N⦄ t₁)
  · specialize a h
    simp_all
    grind
  · simp_all
    grind

end Nets
