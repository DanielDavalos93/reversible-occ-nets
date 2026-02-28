import PetriNet.ReversibleOcc
import PetriNet.Swapping
open ReversibleOcc

variable {α β : Type} [DecidableEq α]

open Nets
open ReversibleNet

/-- ## Trace equivalence
A **trace equivalence** is a equivalence relation `≍` [`\asymp`] if satisfies:
  * `t;t' ≍ t';t` if `t co t'`
  * `t;t' ≍ ε` and `t';t ≍ ε` if `t↽⇀t'`

For a reversible net `R` we denote this relation as `t ≍⦃R⦄ t'`.
-/

inductive TrEq [DecidableEq α] (R : Reversible α β) :
  List (Transition β) → List (Transition β) → Prop
| nil :
  TrEq R [] []
| swap :
  (t t' : Transition β) →
  Disjoint (t•⦃R.toNet⦄) (•⦃R.toNet⦄ t') →
  Disjoint (t'•⦃R.toNet⦄) (•⦃R⦄ t) →
  TrEq R [t, t'] [t', t]
| cancₗ :
  (t t' : Transition β) →
  t ↽⇀ t' →
  TrEq R [t, t'] []
| cancᵣ : (t t' : Transition β) →
  t ↽⇀ t' →
  TrEq R [] [t, t']
| congᵣ : (s₁ s₂ s₃ : List (Transition β)) →
  TrEq R s₁ s₂ →
  TrEq R (s₃ ++ s₁) (s₃ ++ s₂)
| congₗ : (s₁ s₂ s₃ : List (Transition β)) →
  TrEq R s₁ s₂ → TrEq R (s₁ ++ s₃) (s₂ ++ s₃)
| trans : (s₁ s₂ s₃ : List (Transition β)) →
  TrEq R s₁ s₂ → TrEq R s₂ s₃ →
  TrEq R s₁ s₃

notation:50  s₁:51 " ≍⦃" R "⦄ " s₂:51 => TrEq ↑R s₁  s₂

open TrEq TransitionType

open Pl Tr
example : [(t₁, bwd), ↽(t₁, bwd)] ≍⦃R₁⦄ [] := by
  have h : (t₁, bwd) ↽⇀ (↽(t₁, bwd)) := rfl
  exact cancₗ (t₁, bwd) (↽(t₁, bwd)) h

variable {R : Reversible α β}

def TrEq_refl (s : List (Transition β)) : s ≍⦃R⦄ s := by
  induction s with
  | nil => exact nil
  | cons x xs ih =>
    exact (congᵣ xs xs [x] ih)

variable {s s₁ s₂ s₃ s₄ : List (Transition β)}

def TrEq_symm (h : s₁ ≍⦃R⦄ s₂) : s₂ ≍⦃R⦄ s₁ := by
  induction h with
  | nil => exact nil
  | swap t₁ t₂ e1 e2 => exact swap t₂ t₁ e2 e1
  | cancₗ t₁ t₂ R =>  exact cancᵣ t₁ t₂ R
  | cancᵣ t₁ t₂ R =>  exact cancₗ t₁ t₂ R
  | congₗ  s₁ s₂ s₃ _ ih => exact congₗ s₂ s₁  s₃ ih
  | congᵣ s₁ s₂ s₃ _ ih => exact congᵣ s₂ s₁  s₃ ih
  | trans s₁ s₂ s₃ _ _ ih1 ih2 => exact trans s₃ s₂ s₁  ih2 ih1;

def TrEq_trans (h : s₁ ≍⦃R⦄ s₂) (h' : s₂ ≍⦃R⦄ s₃) : s₁ ≍⦃R⦄ s₃ :=
  trans s₁ s₂ s₃ h h'

lemma TrEq_congruence (h : s₁ ≍⦃R⦄ s₂) (h' : s₃ ≍⦃R⦄ s₄) : s₁ ++ s₃ ≍⦃R⦄ s₂ ++ s₄ := by
  induction h with
  | nil => simp; exact h'
  | swap t t' hco hco' =>
    obtain eq := congₗ [t, t'] [t', t] s₃ (swap t t' hco hco')
    exact trans ([t, t'] ++ s₃) ([t', t] ++ s₃) ([t', t] ++ s₄) eq (congᵣ s₃ s₄ [t', t]  h')
  | cancₗ t t' hrev =>
    obtain eq : [t, t'] ≍⦃R⦄ [] := cancₗ t t' hrev
    exact trans ([t, t'] ++ s₃) s₃ s₄ (congₗ [t, t'] [] s₃ eq) h'
  | cancᵣ t t' hrev =>
    obtain eq : [] ≍⦃R⦄ [t, t']:= cancᵣ t t' hrev
    exact trans s₃ s₄ ([t, t'] ++s₄) h' (congₗ [] [t, t'] s₄ eq)
  | congₗ  l l' l'' hcong  =>
    obtain eq1 := congᵣ (l'' ++ s₃)  (l'' ++ s₄) l (congᵣ s₃ s₄ l'' h')
    obtain eq2 := congₗ l l'  (l'' ++ s₄) hcong
    obtain eq3 := trans (l ++ (l'' ++ s₃)) (l ++ (l'' ++ s₄))  (l' ++ (l'' ++ s₄)) eq1 eq2
    simp_all
  | congᵣ l l' l'' hcong  =>
    obtain eq := trans (l ++ s₃) (l' ++ s₃) (l' ++ s₄) (congₗ l l' s₃ hcong) (congᵣ s₃ s₄ l' h')
    obtain := congᵣ (l ++ s₃) (l' ++ s₄) l'' eq
    simp_all
  | trans l l' l'' eq _ _ ih =>
    exact trans (l ++ s₃) (l' ++ s₃) (l'' ++ s₄) (congₗ l l' s₃ eq) ih

variable {t t' : Transition β}

lemma TrEq_of_cons_left :  t :: s₁ ≍⦃R⦄ s₂ ↔ [t] ++ s₁ ≍⦃R⦄ s₂ := Eq.to_iff rfl

lemma TrEq_of_cons_right : s₁ ≍⦃R⦄ t :: s₂ ↔ s₁ ≍⦃R⦄ [t] ++ s₂ := Eq.to_iff rfl

variable {m₀ m m' : Multiset α}
variable {RO : ReversibleOccurrence α β}

lemma TrEq_swap_fwd_hd_allbwd (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m)
    (ft : ▷t) (bt' : ◁t') (ni : ¬(t ↽⇀ t'))
    (fs : m 〚([t] ++ t' :: s)⟩⟩⦃MO⦄ m') :
    [t, t'] ++ s ≍⦃MO.toReversible⦄ [t', t] ++ s := by
  apply congₗ [t, t'] [t', t] s
  apply swap t t'
  · rw [MO.welldef t' (↽t') (inverse_of_reversing t')]
    apply forward_disjoint_postset (markedRO_to_RO MO) ft (isfwd_iff_reverse_isbwd.mpr bt') ni
  · exact not_reverse_disjoint_post_pre₂ (s:=s) (m':=m') MO rr ni fs

lemma TrEq_swap_exists (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m)
    (ft : ▷t) (bt' : ◁t') (ni : ¬(t ↽⇀ t'))
    (fir : m 〚([t, t'] ++ s)⟩⟩⦃MO⦄ m') :
    m 〚([t', t] ++ s)⟩⟩⦃MO⦄ m' := by
  obtain ⟨m₂, fs₁, fs₂⟩:= append_split_of_fs (ts₁ := [t, t']) fir
  exact concat_fs (swap_fwd_reverse_not_inverse MO rr ft bt' ni fs₁ ) fs₂

variable {s s' : List (Transition β)}

lemma TrEq_swap_fwd_allbwd (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (ft : ▷t) (abw : ◁◁s)
    (hnr : t ∉ʳ s) (fs : m 〚([t] ++ s)⟩⟩⦃MO⦄ m') :
    ([t] ++ s) ≍⦃MO.toReversible⦄ (s ++ [t]) := by
  induction' s  with hd s ih generalizing m m'
  · simp_all [List.append_nil]; exact TrEq_refl [t]
  · obtain i : ¬ t ↽⇀ hd := hnr hd List.mem_cons_self
    obtain fs' := TrEq_swap_exists MO rr ft abw.left i fs
    obtain ⟨m₁, fs₂, fs₃⟩ := append_split_of_fs (ts₁ := [hd]) fs'
    have reach₁ :  m₁ ∈ reachable ⟨MO.toNet, MO.m₀⟩ := by
      unfold reachable is_reachable at *
      obtain ⟨fs'', rr⟩ := rr
      have := concat_fs rr fs₂
      exists fs'' ++ [hd]
    have hnr' : t ∉ʳ s := by
      intros abw' hmem
      exact hnr abw' <| List.mem_cons_of_mem hd hmem
    obtain eq₀ := TrEq_swap_fwd_hd_allbwd MO rr ft abw.left i fs
    obtain eq₁ := congᵣ ([t] ++ s) (s ++ [t]) [hd] <| ih reach₁ abw.right hnr'  fs₃
    exact TrEq_trans eq₀ eq₁

lemma TrEq_swap_fwd_allbw_allfw (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (ft : ▷t) (abw : ◁◁s)
    (ht : t ∉ʳ s) (fs : m 〚[t] ++ s ++ s'⟩⟩⦃MO⦄ m') :
    ([t] ++ s ++ s') ≍⦃MO.toReversible⦄ (s ++ [t] ++ s') := by
  obtain ⟨_, fs', _⟩ := append_split_of_fs  (ts₁ :=[t] ++ s) fs
  exact congₗ ([t] ++ s) (s ++ [t]) s' <| TrEq_swap_fwd_allbwd MO rr  ft abw ht fs'
