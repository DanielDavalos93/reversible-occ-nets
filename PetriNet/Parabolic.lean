module

public import PetriNet.Equivalence
public import PetriNet.ReversibleOccurrence
import Architect
open TrEq
open Nets
open ReversibleNet
open ReversibleOcc

@[expose] public section

variable {α β : Type} [DecidableEq α] {RO : ReversibleOccurrence α β}
         {m m' m'' m₀ : Multiset α} {t t' : Transition β}
         {s s' s'' v v' : List (Transition β)}

section Properties_for_parabolic

open List
lemma and_canc_fs (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m)
    (bw : ◁◁(v ++ t' :: v')) (ft : ▷t) (i : t ↽⇀ t') (h : t ∉ʳ v)
    (fs : m 〚t :: v⟩⟩⦃MO⦄ m')
    (eq : s ≍⦃MO.toReversible⦄ ((v ++ t' :: v') ++ s')) :
    (t :: s) ≍⦃MO.toReversible⦄ (v ++ v' ++ s') := by
cases fs with
| step e fₜ fs₃ =>
  rw [append_cons, all_bwd_of_append, all_bwd_of_append] at bw
  obtain eq₀ : [] ≍⦃MO.toReversible⦄ [t,t'] := cancᵣ t t' i
  obtain eq₁ := congₗ  (v ++ [t,t']) (v ++ []) (v' ++ s') (TrEq_symm (congᵣ [] [t,t'] v eq₀))
  obtain eq₂ := TrEq_swap_fwd_allbwd MO rr ft (bw.left.left) h (.step e fₜ fs₃)
  obtain eq₃ := congₗ (t :: v ++ [t']) (v ++ [t] ++ [t']) (v' ++ s')
    (congₗ (t :: v) (v ++ [t]) [t'] eq₂)
  rw [append_cons, append_nil] at eq₁
  obtain eq₄ := trans ([t] ++ v ++ [t'] ++ (v' ++ s')) (v ++ [t] ++ [t'] ++ (v' ++ s'))
    (v ++ (v' ++ s')) eq₃ eq₁
  rw [append_cons, append_assoc,append_assoc] at *
  have eq₅ := congᵣ s (v ++ t':: (v' ++ s')) [t] eq
  apply trans (t :: s) (t:: (v ++ (t':: v' ++ s'))) (v ++ (v' ++ s')) eq₅ eq₄

-- Abreviation for Parabolic statement
def parabolic_decomp (s s' s'' : List (Transition β)) (m m' : Multiset α) :=
  ◁◁s' ∧ ▷▷s'' ∧ m 〚s' ++ s''⟩⟩⦃RO⦄ m' ∧ s ≍⦃RO.toReversible⦄ (s' ++ s'')

lemma concat_canc_firing_sequence (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) {eₜ : m 〚t〛⦃MO⦄}
    (f : m 〚eₜ⟩⦃MO.toNet⦄ m'') (ft : ▷t)
    (P : ∃ s' s'', parabolic_decomp (RO := markedRO_to_RO MO) s s' s'' m'' m' ∧ ¬ t ∉ʳ s') :
    ∃ s' s'', parabolic_decomp (RO := markedRO_to_RO MO) (t :: s) s' s'' m m' := by
  obtain ⟨s', s'', ⟨bw, _, fs, eq₀⟩, h⟩ := P
  rw [not_no_reverse_iff_exists_reverse] at h
  obtain ⟨v, v', _, i, _, hi⟩ := fst_split_not_rev bw h
  obtain ⟨_, fs₁, fs₂⟩ := append_split_of_fs fs
  subst_eqs
  obtain ⟨n, fs₃, fs₄⟩ := append_split_of_fs  fs₁
  obtain ⟨bw', bw''⟩  := all_bwd_of_append.mp bw
  obtain ⟨n', fs₅, fs₆⟩ := append_split_of_fs <| swapping MO rr bw' ft hi (.step eₜ f fs₃)
  cases fs₄ with
  | step e f' fs' =>
    obtain := fs_rev_empty (RO := markedRO_to_RO MO) (inverse_symm.mpr i) <|
      concat_fs fs₆ <| .step e f' (.empty _)
    subst_eqs
    exists v ++ v', s''
    obtain fsc := concat_fs (concat_fs fs₅ fs') fs₂
    obtain treq := and_canc_fs MO rr bw ft (inverse_symm.mp i) hi (.step eₜ f fs₃) eq₀
    obtain := all_bwd_of_append.mpr (And.intro bw' bw''.right)
    simp_all [parabolic_decomp]
    exact ⟨fsc, treq⟩

--Forward case for the head of the list of transitions `s` in parabolic
@[blueprint "lem:parabolic_step_fwd"
 (statement := /-- Step of forward case for parabolic. -/)
 (proofUses := ["lem:concat_fs", "lem:swapping"])
 (hasProof := false)
 (latexEnv := "lemma")]
lemma parabolic_step_fwd (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) {eₜ : m 〚t〛⦃MO⦄}
    (fₜ : m 〚eₜ⟩⦃MO.toNet⦄ m'')
    (ft : ▷t) (bw : ◁◁s') (fw : ▷▷s'')
    (fs : m'' 〚s' ++ s''⟩⟩⦃MO⦄ m') (eq : s ≍⦃MO.toReversible⦄ (s' ++ s'')) :
    ∃ s' s'', parabolic_decomp (RO := markedRO_to_RO MO) (t :: s) s' s'' m m' := by
  by_cases h : ( ∀ t' ∈ s', ¬ (t ↽⇀ t'))
  · exists s', [t] ++ s''
    obtain eq₁ := TrEq_swap_fwd_allbw_allfw MO rr ft bw h (.step eₜ fₜ fs)
    constructor
    · exact bw
    · obtain ⟨_, fs₀, fs₁⟩ := append_split_of_fs fs
      obtain fs' := concat_fs (swapping MO rr bw ft h (.step eₜ fₜ fs₀)) fs₁
      · repeat constructor
        · exact ft
        · exact fw
        · obtain heq := congᵣ s (s' ++ s'') [t] eq
          simp; rw [append_cons]
          exact ⟨fs', trans ([t] ++ s) ([t] ++ s' ++ s'') (s' ++ [t] ++ s'') heq eq₁⟩
  · exact concat_canc_firing_sequence MO rr fₜ ft ⟨s', s'', ⟨bw, fw, fs, eq⟩, h⟩

end Properties_for_parabolic


/-! ### Main result
-/
@[blueprint "thm:parabolic"
 (title := /-- Parabolic lemma -/)
 (statement := /--Let $R$ be a reversible occurrence net, $m$ a reachable marking, and 
 $m [[\omega⟫ m'$ a firing sequence. Then there exist two sequences of transitions, $\omega'$ and
  $\omega''$, such that $\omega'$ consists only of backward transitions, $\omega''$
  consists only of forward transitions, $\omega ≍  \omega';\omega''$,
  and $m [[\omega'; \omega''⟫ m'$. -/)
  (proof := /-- By applying induction on the firing sequence. The base case when $m' = m$ is 
  immediate. The inductive step applies the property of $≍ $ and the 
  Lemma \ref{lem:parabolic_step_fwd}.-/)
  (proofUses := ["lem:parabolic_step_fwd", "lem:concat_fs", "def:TrEq"])]
theorem parabolic (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m)
    (fs : m 〚s⟩⟩⦃MO⦄ m') : ∃ s' s'', parabolic_decomp (RO := markedRO_to_RO MO) s s' s'' m m' := by
  induction fs with
  | @empty m =>
      exists [], []
      simp_all [parabolic_decomp, all_backward, all_forward]
      exact ⟨.empty m, TrEq_refl []⟩
  | @step t fs' m m₁ _ et f _ IH  =>
    unfold parabolic_decomp
    have rr' : m₁ ∈ reachable ⟨MO.toNet, MO.m₀⟩ := by
      obtain ⟨s, fs⟩ := rr
      obtain := concat_fs fs (.step et f (.empty _))
      exists s ++ [t]
    obtain ⟨s', s'', a, b, fs, eq⟩ := IH rr'
    by_cases h : isBwd t
    · obtain := firing_sequence.step et f fs
      obtain : (t :: fs') ≍⦃MO.toReversible⦄ (t :: (s' ++ s'')) := congᵣ fs' (s' ++ s'') [t] eq
      exists (t :: s'), s''
    · obtain ⟨s', s'', _⟩ :=  parabolic_step_fwd MO rr f (is_fwd_of_not_bwd h) a b fs eq
      exists s', s''
