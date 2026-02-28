import PetriNet.ReversibleOcc
import PetriNet.MultisetAux
import PetriNet.Occurrence

open Nets ReversibleNet ReversibleOcc
open Multiset
open Nat
open Relation Relation.TransGen


/-! ### Swapping
  In this file we proved lemmas about swap a forward transition `t` on a backward list `ω`:
 ``
-/

variable {α β : Type}
variable {t t' : Transition β} {m₀ m m' : Multiset α} {s : List (Transition β)}

def no_rev_in_list (t : Transition β) (ls : List (Transition β)) :=
  ∀ t' ∈ ls, ¬ (t ↽⇀ t')

infix:50 " ∉ʳ " => no_rev_in_list

def exists_rev_in_list (t : Transition β) (ls : List (Transition β)) :=
  ∃ t' ∈ ls, t ↽⇀ t'

infix:50 " ∃ʳ " => exists_rev_in_list

lemma not_no_reverse_iff_exists_reverse : ¬ t ∉ʳ s ↔  t ∃ʳ s := by
  unfold no_rev_in_list exists_rev_in_list; simp

lemma not_reverse_disjoint_post_pre [DecidableEq α] (RO : ReversibleOccurrence α β)
    (ft : ▷t) (bt' : ◁t') : t ↽⇀ t' ∨ Disjoint (t•⦃RO.toNet⦄) (•⦃RO.toNet⦄ t') := by
  by_cases h : (t ↽⇀ t')
  · left; assumption
  · right
    obtain := forward_disjoint_postset RO ft (isfwd_iff_reverse_isbwd.mpr bt') h
    obtain := RO.welldef t' (↽t') (inverse_of_reversing t')
    simp_all

variable {M : MarkedNet α β} {t t' : Transition β}

lemma disj_post_pre_disjoint_pre_post_occ [DecidableEq α] (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (fs : m 〚[t, t']⟩⟩⦃MO⦄ m')
    (h : Disjoint (t•⦃MO.toNet⦄) (•⦃MO.toNet⦄t')) : Disjoint t'•⦃MO.toNet⦄ (•⦃MO.toNet⦄ t) := by
  obtain ⟨m₁, _ | ⟨e, f₁, fs₁⟩, _ | ⟨e', _, _⟩ ⟩ := append_split_of_fs (ts₁ := [t]) fs
  obtain := target_of_empty_fs fs₁
  subst_eqs
  have rr' : ⟨MO.toNet, MO.m₀⟩ ↝ m₁ := reach_after_firing_from_reach rr f₁
  obtain  eₜ' := can_swap_if_disjoint_pre_post fs h
  obtain rr' := reach_after_firing_from_reach rr <| is_firing_of_enabled eₜ'
  obtain sa := reversible_occ_net_safe MO
  unfold safe reachable is_reachable at sa
  specialize sa (m -  (•⦃MO.toNet⦄ t') + (t'•⦃MO.toNet⦄)) rr'
  obtain nd : ∀ (a : α), count a (m - (•⦃MO.toNet⦄ t') + (t'•⦃MO.toNet⦄)) ≤ 1 :=
    nodup_iff_count_le_one.mp  <| sa
  contrapose! nd
  obtain ⟨a, ha₁, ha₂⟩ := exists_mem_of_ne_zero (mt inter_eq_zero_iff_disjoint.mp nd)
          |>.imp (fun _ => mem_inter.mp)
  exists a
  have hy: a ∈ m := Multiset.mem_of_le e ha₂
  have hn : a ∉ (•⦃MO.toNet⦄ t') := by
    rcases t' with ⟨val , fwd | bwd⟩
    · have hyh: a ∈ (val •⦃fwd_subnet MO.toNet⦄) := by exact ha₁
      obtain a_notin := not_mem_pre_of_mem_pre MO.isFwdMarkedOcurrence.occurrence hyh
      unfold fwd_subnet presetₜ at *
      exact a_notin
    · have h : ⟨val, .bwd⟩  ↽⇀ ⟨val, .fwd⟩ := rfl
      obtain hyh := (in_post_bwd_iff_in_pre_fwd (R := MO.toReversible)  h).mp ha₁
      obtain := not_mem_post_of_mem_pre MO.isFwdMarkedOcurrence.occurrence hyh
      intro hh
      have a_in := (mem_pre_fwd_iff_mem_post_bwd (R := MO.toReversible) h).mp hh
      unfold fwd_subnet postsetₜ at *
      contradiction
  rw [count_add, count_sub, count_eq_zero.mpr hn, Nat.sub_zero]
  obtain := count_pos.mpr hy
  obtain := count_pos.mpr ha₁
  grind

lemma not_reverse_disjoint_pre_post_occ [DecidableEq α] (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (fs : m 〚[t, t']⟩⟩⦃MO⦄ m') (nrev : ¬t ↽⇀ t')
    (h : ¬Disjoint (t•⦃MO.toNet⦄) (•⦃MO.toNet⦄ t')) : Disjoint t'•⦃MO.toNet⦄ (•⦃MO.toNet⦄ t) := by
  obtain ⟨m₁, _ | ⟨e, f₁, fs₁⟩, _ | ⟨e', _, _⟩ ⟩ := append_split_of_fs (ts₁ := [t]) fs
  obtain := target_of_empty_fs fs₁
  subst_eqs
  have rr' : ⟨MO.toNet, MO.m₀⟩ ↝ m₁ := reach_after_firing_from_reach rr f₁
  rcases t with ⟨val, fwd | bwd⟩
  · rcases t' with ⟨val', fwd' | bwd'⟩
    · by_contra hh
      have := cycle_from_shared_pre_post (N := fwd_subnet MO.toNet) h hh
      have := MO.isFwdMarkedOcurrence.occurrence.acyclicity
      contradiction
    · have i : ⟨val', .bwd⟩  ↽⇀ ⟨val', .fwd⟩ := rfl
      obtain hh := concurrent_marking_of_reversible_occ_net MO rr'
      contrapose! hh
      obtain ⟨a, ha₁, ha₂⟩ := exists_mem_of_ne_zero (mt inter_eq_zero_iff_disjoint.mp hh)
                      |>.imp (fun _ => mem_inter.mp)
      have ri := MO.welldef ⟨val', .bwd⟩ ⟨val', .fwd⟩ i
      have ri' := MO.welldef ⟨val', .fwd⟩ ⟨val', .bwd⟩ (inverse_symm.mpr i)
      rw [ri] at h
      rw [symm ri'] at hh
      have ne : val' ≠ val := by exact fun a ↦ nrev (
        congrFun (congrArg Prod.mk (id (Eq.symm a))) TransitionType.fwd)
      have h' : ¬ Disjoint (•⦃fwd_subnet MO.toNet⦄ val') (•⦃fwd_subnet MO.toNet⦄ val) := by
        unfold fwd_subnet presetₜ at *
        exact hh
      have ic := immediate_conflict_of_shared_pre (N := fwd_subnet MO.toNet) ne h'
      have e₁ : (val' •⦃(fwd_subnet MO.toNet)⦄ ) ≤ m₁ := le_of_eq_of_le (id (Eq.symm ri)) e'
      have e₂ : (val •⦃(fwd_subnet MO.toNet)⦄ ) ≤ m₁ := by
        unfold is_firing marking_after_firing at f₁
        obtain := le_add_left (val •⦃(fwd_subnet MO.toNet)⦄) <| m - (•⦃(fwd_subnet MO.toNet)⦄ val)
        simp_all [fwd_subnet]
      obtain ⟨ta, hta⟩ := exists_mem_of_ne_zero <|
             ((fwd_subnet MO.toNet).cons_prod val').right
      obtain ⟨tb, htb⟩ := Multiset.exists_mem_of_ne_zero <|
            ((fwd_subnet MO.toNet).cons_prod val).right
      have cta := Flow.causal_of_mem_post hta
      have ctb := Flow.causal_of_mem_post htb
      have hh : (.inl ta #⦃(fwd_subnet MO.toNet)⦄ .inl tb) := by
        unfold conflict
        exists val', val
        simp_all only [ne_eq, Flow.preorder_of_causal, immediate_conflict_symm, and_self]
      have hta' := mem_of_le e₁ hta
      have htb' := mem_of_le e₂ htb
      have d : Disjoint (val' •⦃(fwd_subnet MO.toNet)⦄ ) (val •⦃(fwd_subnet MO.toNet)⦄ ) := by
        have fwd_val' : ▷(val', .fwd) := rfl
        have fwd_val : ▷(val, .fwd) := rfl
        have neTransType :  (val', TransitionType.fwd) ≠ (val, TransitionType.fwd) := by
          exact fun a ↦ nrev (id (Eq.symm a))
        exact forward_disjoint_postset ⟨MO.toReversible, MO.isFwdMarkedOcurrence.occurrence⟩
          fwd_val' fwd_val neTransType
      have ne : ta ≠ tb :=  disjoint_iff_ne.mp d ta hta tb htb
      simp [Concurrent, concurrent]; intros
      exists ta, hta', tb, htb', ne
      exact fun _ _ _ _ _ ↦ hh
  · rcases t' with ⟨val', fwd' | bwd'⟩
    · have i : ⟨val, .bwd⟩  ↽⇀ ⟨val, .fwd⟩ := rfl
      obtain hh := concurrent_marking_of_reversible_occ_net MO rr'
      contrapose! hh
      have ri := MO.welldef ⟨val, .bwd⟩ ⟨val, .fwd⟩ i
      have ri' := MO.welldef ⟨val, .fwd⟩ ⟨val, .bwd⟩ (inverse_symm.mpr i)
      rw [←ri'] at h
      rw [ri] at hh
      have d : ¬ Disjoint (val' •⦃(fwd_subnet MO.toNet)⦄ ) (val •⦃(fwd_subnet MO.toNet)⦄ ) := by
            simp_all [fwd_subnet]
      obtain ⟨a, ha₁, ha₂⟩ := exists_mem_of_ne_zero (mt inter_eq_zero_iff_disjoint.mp d)
                  |>.imp (fun _ => mem_inter.mp)
      have bwc := MO.isFwdMarkedOcurrence.occurrence.no_backward_conflict a
      contrapose! bwc
      have ne : val' ≠ val := by exact fun a ↦ nrev <| congrFun (
        congrArg Prod.mk (id (Eq.symm a))) TransitionType.bwd
      exists val', val, ne
    · have i : ⟨val, .bwd⟩  ↽⇀ ⟨val, .fwd⟩ := rfl
      have i' : ⟨val', .bwd⟩  ↽⇀ ⟨val', .fwd⟩ := rfl
      have ri := MO.welldef ⟨val', .bwd⟩ ⟨val', .fwd⟩ i'
      rw [ri] at h
      rw [symm (MO.welldef ⟨val', .fwd⟩ ⟨val', .bwd⟩ (inverse_symm.mpr i'))]
      have ri' := MO.welldef ⟨val, .fwd⟩ ⟨val, .bwd⟩ (inverse_symm.mpr i)
      rw [←ri'] at h
      rw [MO.welldef ⟨val, .bwd⟩ ⟨val, .fwd⟩ i]
      obtain ⟨a, ha₁, ha₂⟩ := exists_mem_of_ne_zero (mt inter_eq_zero_iff_disjoint.mp h)
                  |>.imp (fun _ => mem_inter.mp)
      by_contra d
      obtain ⟨b, hb₁, hb₂⟩ := exists_mem_of_ne_zero (mt inter_eq_zero_iff_disjoint.mp d)
                  |>.imp (fun _ => mem_inter.mp)
      have ha₁' : a ∈ •⦃(fwd_subnet MO.toNet)⦄ val := by exact ha₁
      have ha₂' : a ∈ val' •⦃(fwd_subnet MO.toNet)⦄ := by exact ha₂
      have hb₁' : b ∈ •⦃(fwd_subnet MO.toNet)⦄ val' := by exact hb₁
      have hb₂' : b ∈ val •⦃(fwd_subnet MO.toNet)⦄ := by exact hb₂
      have c1 := Flow.causal_of_mem_post ha₂'
      have c2 := Flow.causal_of_mem_post hb₂'
      have c3 := Flow.causal_of_mem_pre hb₁'
      have c4 := Flow.causal_of_mem_pre ha₁'
      have hh : (.inr val' ) ≺⦃fwd_subnet MO.toNet⦄ (.inr val) := .trans c1 c4
      have hh' : (.inr val) ≺⦃fwd_subnet MO.toNet⦄ (.inr val')  := .trans c2 c3
      have cycle: (.inr val' ) ≺⦃fwd_subnet MO.toNet⦄ (.inr val')  := .trans hh hh'
      have ac := MO.isFwdMarkedOcurrence.occurrence.acyclicity
      unfold acyclic at ac
      specialize ac (.inr val')
      simp_all [fwd_subnet]

variable [DecidableEq α] {RO : ReversibleOccurrence α β} {t t' : Transition β}

lemma not_reverse_disjoint_pre_post (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (fs : m 〚[t, t']⟩⟩⦃MO⦄ m') :
    t' ↽⇀ t ∨ (Disjoint (t'•⦃MO.toNet⦄) (•⦃MO.toNet⦄ t)) := by
  by_cases hrev : (t ↽⇀ t')
  · rw [inverse_symm] at hrev; exact (Or.inl hrev)
  · right
    obtain ⟨m₁, _ | ⟨e, f₁, fs₁⟩, _ | ⟨e', _, _⟩ ⟩ := append_split_of_fs (ts₁ := [t]) fs
    obtain := target_of_empty_fs fs₁
    subst_eqs
    by_cases h : Disjoint (t•⦃MO.toNet⦄) (•⦃MO.toNet⦄ t')
    · exact disj_post_pre_disjoint_pre_post_occ MO rr fs h
    · exact not_reverse_disjoint_pre_post_occ MO rr fs hrev h

lemma not_reverse_disjoint_post_pre₂ (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (ni : ¬t ↽⇀ t') (fs : m 〚([t] ++ t' :: s)⟩⟩⦃MO⦄ m') :
    Disjoint t'•⦃MO.toNet⦄ (•⦃MO.toNet⦄ t) := by
  rw [List.append_cons] at fs
  obtain ⟨_, fs₂, _⟩ := append_split_of_fs fs
  cases (not_reverse_disjoint_pre_post (MO := MO) rr fs₂) with
  | inl rev' => rw [inverse_symm] at rev' ; exact False.elim (ni rev')
  | inr nrev => exact nrev

lemma swap_fwd_bwd_pre_post_empty (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m)
    (_ : ¬t ↽⇀ t') (b : m 〚[t, t']⟩⟩⦃MO⦄ m')
    (d₁ : Disjoint t•⦃MO.toNet⦄ (•⦃MO⦄t')) : m〚[t', t]⟩⟩⦃MO⦄ m' := by
  rcases not_reverse_disjoint_pre_post MO rr b with r₂ | d₂
  · simp_all
  · obtain _ | ⟨e₀, f₀, _ | ⟨ e₁, f₁, ⟨_⟩ ⟩ ⟩ := b
    unfold is_enabled is_firing marking_after_firing at *;
    subst_eqs
    obtain := disjoint_sub_add_sub_add_comm (m:=m) d₁ d₂
    rw [←disjoint_comm] at d₁ d₂
    have e₂' : (m - •⦃MO.toNet⦄ t' + t'•⦃MO.toNet⦄)〚t〛⦃MO⦄ := by
      have le : •⦃MO.toNet⦄t ≤ m - •⦃MO.toNet⦄t' + t'•⦃MO.toNet⦄ := by
        obtain ⟨e₁', e₂'⟩ := Multiset.le_iff_exists_add.mp
            <| le_of_le_sub_le_sub (le_of_le_add_of_disjoint d₁ e₁) e₀
        apply Multiset.le_iff_exists_add.2
        exists (e₁'+ t'•⦃MO.toNet⦄)
        rw [e₂', Multiset.add_assoc]
      exact le
    have eq : (m - •⦃MO.toNet⦄t' + t'•⦃MO.toNet⦄ - •⦃MO.toNet⦄t + t•⦃MO.toNet⦄) =
      (m - •⦃MO.toNet⦄t + t•⦃MO.toNet⦄ - •⦃MO.toNet⦄t' + t'•⦃MO.toNet⦄) := by grind
    rw [← eq]
    obtain e₁' := is_enabled_from <|
       le_trans (le_of_le_add_of_disjoint d₁ e₁) (Multiset.sub_le_self m (•⦃MO.toNet⦄ t ))
    exact .step e₁' (is_firing_of_enabled e₁') <| .step e₂'
      (is_firing_of_enabled (is_enabled_from e₂')) (.empty _)

lemma swap_fwd_reverse_not_inverse (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m) (ft : ▷t) (bt' : ◁t') (ni : ¬ t ↽⇀ t')
    (fs : m 〚[t, t']⟩⟩⦃MO⦄ m') : m 〚[t',t]⟩⟩⦃MO⦄ m':= by
  rcases not_reverse_disjoint_post_pre ⟨MO.toReversible, MO.isFwdMarkedOcurrence.occurrence⟩
    ft bt' with r₁ | d₁
  · contradiction
  · exact swap_fwd_bwd_pre_post_empty MO rr ni fs d₁

lemma fs_rev_empty (i : t ↽⇀ t') (fs : m 〚[t, t']⟩⟩⦃RO⦄ m') :  m = m' := by
  obtain pre_post_tt' := eq_pre_post_of_inverse RO.toReversible i
  obtain pre_post_t't := eq_pre_post_of_inverse RO.toReversible (inverse_symm.mpr i)
  obtain _| ⟨e₀, f₀,  _ | ⟨_, f₁, ⟨_⟩ ⟩ ⟩ := fs
  · rw [is_firing, marking_after_firing] at *; rename_i m''; subst f₀ f₁
    obtain cancel := submultiset_cancelation (s:= m) (t := •⦃RO.toNet⦄t) e₀
    rw [pre_post_t't, ←pre_post_tt', Multiset.add_sub_cancel_right, Multiset.add_comm]
    exact (symm cancel)

/-- A forward transition `t` can be swapped with a backward sequence `ω` if there
a firing sequence that passes through the sequence `t :: ω`
-/
lemma swapping (MO : MarkedReversibleOccurrence α β)
    (rr : ⟨MO.toNet, MO.m₀⟩ ↝ m)
    (bw : ◁◁s) (ft : ▷t) (nrev : t ∉ʳ s)
    (fs : m 〚t :: s⟩⟩⦃MO⦄ m') :  m 〚s ++ [t]⟩⟩⦃MO⦄ m' := by
  induction s generalizing m with
  | nil =>
    simp_all
  | cons hd s s_ih =>
    obtain _| ⟨e₀, f₀,  _ | ⟨ e₁, f₁, fs₁ ⟩ ⟩ := fs
    obtain ⟨bhd, btl⟩ := bw
    obtain ⟨nohd, notl⟩ := List.forall_mem_cons.mp nrev
    obtain fs' := firing_sequence.step e₀ f₀ <| .step e₁ f₁ (.empty _)
    obtain _ | ⟨e₀', f₀', fs₀'⟩ :=
      swap_fwd_reverse_not_inverse MO rr ft bhd nohd fs'
    exact firing_sequence.step e₀' f₀' <|
      s_ih (reach_after_firing_from_reach rr f₀') btl notl <| concat_fs fs₀' fs₁

lemma tr_in_list_bwd {hd} (h : t' ∈ hd :: s) (_ : t ↽⇀ t') (_ : ¬hd ↽⇀ t) : t' ∈ s := by
  rw [List.mem_cons] at h
  cases h with
  | inl x => simp_all
  | inr x => exact x

lemma fst_split_not_rev {ω} (abw : ◁◁ω) (h : t ∃ʳ ω) :
    ∃ s s' t', t' ↽⇀ t ∧ ω = s ++ t' :: s' ∧ t ∉ʳ s := by
  induction ω with
    | nil =>
      exists [], []
      simp [exists_rev_in_list] at h
    | cons hd tl ih =>
      obtain ⟨t₁, h₁, w₁⟩ := h
      obtain ⟨_, bw_tl⟩ := abw
      by_cases h : (hd ↽⇀ t)
      · exists [], tl, hd
        simp only [List.nil_append, List.not_mem_nil, no_rev_in_list, IsEmpty.forall_iff,
          implies_true, and_true]
        exact h
      · have ht₁_tl : t₁ ∈ tl := tr_in_list_bwd h₁ w₁ h
        obtain ⟨s₁, s₂, t₂, _, _, h₂⟩ := ih bw_tl ⟨t₁, tr_in_list_bwd h₁ w₁ h, w₁⟩
        exists (hd :: s₁), s₂, t₂
        simp_all only [List.cons_append, true_and]
        intros t₃ h
        obtain _ | itl := List.mem_cons.mp h
        · simp_all
        · unfold no_rev_in_list at h₂; exact h₂ t₃ itl
