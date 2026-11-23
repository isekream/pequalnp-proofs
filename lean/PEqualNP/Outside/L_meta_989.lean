import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989

open MvPolynomial
open Classical



lemma dep_of_cross {F : Type} [Field F] {x y : Fin 3 → F} (hx : x ≠ 0)
    (h : crossProduct x y = 0) : ∃ a : F, a • x = y := by
  have hli : ¬ LinearIndependent F ![x, y] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]; exact not_not.mpr h
  rw [LinearIndependent.pair_iff' hx] at hli
  simp only [not_forall, not_not] at hli
  exact hli

lemma forms_prop {F : Type} [Field F] (v w m m' : Fin 3 → F) (hv : v ≠ 0)
    (hvw : ∀ c : F, w ≠ c • v) (hm : m ≠ 0)
    (h1 : v ⬝ᵥ m = 0) (h2 : w ⬝ᵥ m = 0) (h3 : v ⬝ᵥ m' = 0) (h4 : w ⬝ᵥ m' = 0) :
    ∃ c : F, m' = c • m := by
  by_cases hu : crossProduct m m' = 0
  · obtain ⟨a, ha⟩ := dep_of_cross hm hu
    exact ⟨a, ha.symm⟩
  · exfalso
    have key : ∀ x : Fin 3 → F, x ⬝ᵥ m = 0 → x ⬝ᵥ m' = 0 →
        crossProduct (crossProduct m m') x = 0 := by
      intro x hx hx'
      rw [← cross_anticomm, cross_cross_eq_smul_sub_smul', hx', dotProduct_comm, hx]
      simp
    obtain ⟨a, ha⟩ := dep_of_cross hu (key v h1 h3)
    obtain ⟨a', ha'⟩ := dep_of_cross hu (key w h2 h4)
    have ha0 : a ≠ 0 := by
      rintro rfl; apply hv; rw [← ha]; simp
    apply hvw (a' / a)
    rw [← ha', ← ha, smul_smul, div_mul_cancel₀ _ ha0]




noncomputable def lin {F : Type} [Field F] (u : Fin 3 → F) : MvPolynomial (Fin 3) F :=
  ∑ t, C (u t) * X t

lemma lin_hom {F : Type} [Field F] (u : Fin 3 → F) : (lin u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun t _ => isHomogeneous_C_mul_X (u t) t)

lemma eval_lin {F : Type} [Field F] (u v : Fin 3 → F) : eval v (lin u) = u ⬝ᵥ v := by
  simp [lin, dotProduct]

lemma card_M (b : ℕ) : (Finset.univ.finsuppAntidiag b : Finset (Fin 3 →₀ ℕ)).card =
    (b + 2).choose 2 := by
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show 3 + b - 1 = b + 2 by omega, Nat.choose_symm_add]

lemma mem_M {F : Type} [Field F] {b : ℕ} {φ : MvPolynomial (Fin 3) F} (h : φ.IsHomogeneous b) :
    φ ∈ restrictSupport F (↑(Finset.univ.finsuppAntidiag b : Finset (Fin 3 →₀ ℕ))) := by
  rw [mem_restrictSupport_iff]
  intro d hd
  have hd' : d.degree = b := by
    have := h (mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_weight_one]; exact this
  rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
  exact ⟨by rw [← Finsupp.degree_eq_sum]; exact hd', Finset.subset_univ _⟩

lemma core {F : Type} [Field F] (k b : ℕ) (P : Fin k → MvPolynomial (Fin 3) F)
    (l : Fin k → Fin 3 → F) (hP : ∀ i, (P i).IsHomogeneous b)
    (hdiag : ∀ i, eval (l i) (P i) ≠ 0) (hoff : ∀ i j, i ≠ j → eval (l j) (P i) = 0) :
    k ≤ (b + 2).choose 2 := by
  set M : Finset (Fin 3 →₀ ℕ) := Finset.univ.finsuppAntidiag b
  let V := restrictSupport F (↑M : Set (Fin 3 →₀ ℕ))
  let B := basisRestrictSupport F (↑M : Set (Fin 3 →₀ ℕ))
  have : Module.Finite F V := Module.Finite.of_basis B
  let Q : Fin k → V := fun i => ⟨P i, mem_M (hP i)⟩
  have hli : LinearIndependent F Q := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : (∑ i, g i • P i) = 0 := by
      have := congrArg (fun z : V => (z : MvPolynomial (Fin 3) F)) hg
      simpa [Q] using this
    have h2 := congrArg (eval (l j)) h1
    rw [map_sum, map_zero, Finset.sum_eq_single j] at h2
    · simp only [smul_eval] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h (hdiag j)
    · intro i _ hij; simp [smul_eval, hoff i j hij]
    · simp
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis B] at this
  simp only [Fintype.card_fin] at this
  have hc : Fintype.card (↑(↑M : Set (Fin 3 →₀ ℕ))) = M.card := by
    simp
  rw [hc, card_M] at this
  exact this


lemma two_choose (b : ℕ) : (b + 1) * (b + 2) = 2 * (b + 2).choose 2 := by
  induction b with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

lemma part1_aux : ∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2) := by
  intro F _ n k b pt l y g hpt0 hptd hl0 hld hyc hyoff hsafe htwo
  -- every other line meets y i
  have hmeet : ∀ i j, i ≠ j → ∃ q ∈ y i, pt q ⬝ᵥ l j = 0 := by
    intro i j hij
    obtain ⟨p, p', hpp, hp, hp', hg, hg'⟩ := htwo i
    obtain ⟨v, hv, hvj⟩ := hsafe j _ hg
    obtain ⟨v', hv', hvj'⟩ := hsafe j _ hg'
    simp only [decide_eq_true_eq] at hv hv'
    rcases hv with hv | rfl
    · exact ⟨v, hv, hvj⟩
    rcases hv' with hv' | rfl
    · exact ⟨v', hv', hvj'⟩
    exfalso
    obtain ⟨c, hc⟩ := forms_prop (pt v) (pt v') (l i) (l j) (hpt0 v) (hptd v v' hpp) (hl0 i)
      hp hp' hvj hvj'
    exact hld i j hij c hc
  have hti : ∀ i, ∃ t, l i t ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hl0 i (funext h)
  choose ti hti using hti
  let P : Fin k → MvPolynomial (Fin 3) F := fun i =>
    (∏ q ∈ y i, lin (pt q)) * X (ti i) ^ (b - (y i).card)
  have hP : ∀ i, (P i).IsHomogeneous b := by
    intro i
    have h1 : (∏ q ∈ y i, lin (pt q)).IsHomogeneous (∑ q ∈ y i, 1) :=
      IsHomogeneous.prod _ _ _ (fun q _ => lin_hom (pt q))
    have h2 := h1.mul ((isHomogeneous_X F (ti i)).pow (b - (y i).card))
    simp only [Finset.sum_const, smul_eq_mul, mul_one, one_mul] at h2
    rwa [show (y i).card + (b - (y i).card) = b by have := hyc i; omega] at h2
  have hev : ∀ i j, eval (l j) (P i) = (∏ q ∈ y i, pt q ⬝ᵥ l j) * (l j (ti i)) ^ (b - (y i).card) := by
    intro i j
    simp [P, eval_lin]
  have hdiag : ∀ i, eval (l i) (P i) ≠ 0 := by
    intro i
    rw [hev]
    refine mul_ne_zero ?_ (pow_ne_zero _ (hti i))
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact hyoff i q hq
  have hoff : ∀ i j, i ≠ j → eval (l j) (P i) = 0 := by
    intro i j hij
    rw [hev]
    obtain ⟨q, hq, hq0⟩ := hmeet i j hij
    rw [Finset.prod_eq_zero hq hq0, zero_mul]
  have := core k b P l hP hdiag hoff
  rw [two_choose]
  omega



noncomputable def nrm {F : Type} [Field F] (v : Fin 3 → F) : Fin 3 → F :=
  if v 0 ≠ 0 then (v 0)⁻¹ • v else if v 1 ≠ 0 then (v 1)⁻¹ • v else (v 2)⁻¹ • v

lemma nrm_eq {F : Type} [Field F] (v : Fin 3 → F) (hv : v ≠ 0) : ∃ c : F, c ≠ 0 ∧ nrm v = c • v := by
  unfold nrm
  by_cases h0 : v 0 ≠ 0
  · exact ⟨(v 0)⁻¹, inv_ne_zero h0, by simp [h0]⟩
  by_cases h1 : v 1 ≠ 0
  · exact ⟨(v 1)⁻¹, inv_ne_zero h1, by simp [h0, h1]⟩
  have h2 : v 2 ≠ 0 := by
    intro h2; apply hv; funext t; fin_cases t <;> simp_all
  exact ⟨(v 2)⁻¹, inv_ne_zero h2, by simp [h0, h1]⟩

lemma nrm_smul {F : Type} [Field F] (v : Fin 3 → F) (c : F) (hc : c ≠ 0) : nrm (c • v) = nrm v := by
  unfold nrm
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or, smul_smul]
  split_ifs <;> congr 1 <;> field_simp

lemma nrm_ne {F : Type} [Field F] (v : Fin 3 → F) (hv : v ≠ 0) : nrm v ≠ 0 := by
  obtain ⟨c, hc, h⟩ := nrm_eq v hv
  rw [h]; exact smul_ne_zero hc hv

lemma nrm_nrm {F : Type} [Field F] (v : Fin 3 → F) (hv : v ≠ 0) : nrm (nrm v) = nrm v := by
  obtain ⟨c, hc, h⟩ := nrm_eq v hv
  conv_lhs => rw [h]
  exact nrm_smul v c hc

lemma L_fin {F : Type} [Field F] (s t u : F) : ![1, u, u ^ 2] ⬝ᵥ (crossProduct ![1, s, s ^ 2] ![1, t, t ^ 2]) =
    (t - s) * (u - s) * (u - t) := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring

lemma L_inf3 {F : Type} [Field F] (s t : F) : ![0, 0, 1] ⬝ᵥ (crossProduct ![1, s, s ^ 2] ![1, t, t ^ 2]) = t - s := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]

lemma L_inf1 {F : Type} [Field F] (t u : F) : ![1, u, u ^ 2] ⬝ᵥ (crossProduct ![0, 0, 1] ![1, t, t ^ 2]) = u - t := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring

lemma L_inf2 {F : Type} [Field F] (s u : F) : ![1, u, u ^ 2] ⬝ᵥ (crossProduct ![1, s, s ^ 2] ![0, 0, 1]) = s - u := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring

noncomputable def arc {F : Type} [Field F] {b : ℕ} (τ : Fin (b + 1) → F) : Fin (b + 2) → Fin 3 → F := fun m =>
  if h : (m : ℕ) < b + 1 then ![1, τ ⟨m, h⟩, τ ⟨m, h⟩ ^ 2] else ![0, 0, 1]

lemma tne {F : Type} [Field F] {b : ℕ} {τ : Fin (b + 1) → F} (hτ : Function.Injective τ) {m m' : Fin (b + 2)}
    (h : (m : ℕ) < b + 1) (h' : (m' : ℕ) < b + 1) (hne : m ≠ m') :
    τ ⟨m, h⟩ ≠ τ ⟨m', h'⟩ := by
  intro e
  have := hτ e
  apply hne
  exact Fin.ext (by simpa using congrArg Fin.val this)

lemma last_eq {b : ℕ} {m m' : Fin (b + 2)} (h : ¬ (m : ℕ) < b + 1) (h' : ¬ (m' : ℕ) < b + 1) :
    m = m' := by
  have := m.isLt; have := m'.isLt
  exact Fin.ext (by omega)

lemma arc_tri {F : Type} [Field F] {b : ℕ} {τ : Fin (b + 1) → F} (hτ : Function.Injective τ) (m1 m2 m3 : Fin (b + 2))
    (h12 : m1 ≠ m2) (h13 : m1 ≠ m3) (h23 : m2 ≠ m3) :
    arc τ m3 ⬝ᵥ crossProduct (arc τ m1) (arc τ m2) ≠ 0 := by
  by_cases h1 : (m1 : ℕ) < b + 1 <;> by_cases h2 : (m2 : ℕ) < b + 1 <;>
    by_cases h3 : (m3 : ℕ) < b + 1
  · simp only [arc, dite_eq_left h1, dite_eq_left h2, dite_eq_left h3]
    rw [L_fin]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> rw [sub_ne_zero]
    · exact tne hτ h2 h1 (Ne.symm h12)
    · exact tne hτ h3 h1 (Ne.symm h13)
    · exact tne hτ h3 h2 (Ne.symm h23)
  · simp only [arc, dite_eq_left h1, dite_eq_left h2, dite_eq_right h3]
    rw [L_inf3, sub_ne_zero]; exact tne hτ h2 h1 (Ne.symm h12)
  · simp only [arc, dite_eq_left h1, dite_eq_right h2, dite_eq_left h3]
    rw [L_inf2, sub_ne_zero]; exact tne hτ h1 h3 h13
  · exact absurd (last_eq h2 h3) h23
  · simp only [arc, dite_eq_right h1, dite_eq_left h2, dite_eq_left h3]
    rw [L_inf1, sub_ne_zero]; exact tne hτ h3 h2 (Ne.symm h23)
  · exact absurd (last_eq h1 h3) h13
  · exact absurd (last_eq h1 h2) h12
  · exact absurd (last_eq h1 h2) h12

lemma arc_ne_zero {F : Type} [Field F] {b : ℕ} (τ : Fin (b + 1) → F) (m : Fin (b + 2)) : arc τ m ≠ 0 := by
  unfold arc
  split_ifs with h
  · intro e; have := congrFun e 0; simp at this
  · intro e; have := congrFun e 2; simp at this

lemma arc_nonprop {F : Type} [Field F] {b : ℕ} {τ : Fin (b + 1) → F} (hτ : Function.Injective τ) {m m' : Fin (b + 2)}
    (hne : m ≠ m') (c : F) : arc τ m' ≠ c • arc τ m := by
  by_cases h : (m : ℕ) < b + 1 <;> by_cases h' : (m' : ℕ) < b + 1
  · simp only [arc, dite_eq_left h, dite_eq_left h']
    intro e
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    simp at e0 e1
    rw [← e0, one_mul] at e1
    exact tne hτ h' h (Ne.symm hne) e1
  · simp only [arc, dite_eq_left h, dite_eq_right h']
    intro e
    have e0 := congrFun e 0
    have e2 := congrFun e 2
    simp at e0 e2
    rw [← e0, zero_mul] at e2
    exact one_ne_zero e2
  · simp only [arc, dite_eq_right h, dite_eq_left h']
    intro e
    have e0 := congrFun e 0
    simp at e0
  · exact absurd (last_eq h h') hne



lemma part2_aux : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  intro F _ _ b hb
  -- the points of the plane
  let S : Finset (Fin 3 → F) := (Finset.univ.filter (fun v : Fin 3 → F => v ≠ 0)).image nrm
  have memS : ∀ v : Fin 3 → F, v ≠ 0 → nrm v ∈ S := by
    intro v hv; exact Finset.mem_image.mpr ⟨v, by simp [hv], rfl⟩
  have propS : ∀ u ∈ S, u ≠ 0 ∧ nrm u = u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact ⟨nrm_ne v hv, nrm_nrm v hv⟩
  let eS := S.equivFin
  let pt : Fin S.card → Fin 3 → F := fun p => (eS.symm p : Fin 3 → F)
  have hpt0 : ∀ p, pt p ≠ 0 := fun p => (propS _ (eS.symm p).2).1
  have hptn : ∀ p, nrm (pt p) = pt p := fun p => (propS _ (eS.symm p).2).2
  have hptd : ∀ p p' : Fin S.card, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p := by
    intro p p' hpp c e
    have hc : c ≠ 0 := by rintro rfl; apply hpt0 p'; rw [e, zero_smul]
    have : pt p' = pt p := by rw [← hptn p', e, nrm_smul _ _ hc, hptn]
    apply hpp
    apply eS.symm.injective
    exact Subtype.ext this.symm
  let idxv : ∀ v : Fin 3 → F, v ≠ 0 → Fin S.card := fun v hv => eS ⟨nrm v, memS v hv⟩
  have pt_idxv : ∀ v hv, pt (idxv v hv) = nrm v := by
    intro v hv; simp [pt, idxv]
  have hcov : ∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin S.card) (c : F), v = c • pt p := by
    intro v hv
    obtain ⟨c, hc, h⟩ := nrm_eq v hv
    refine ⟨idxv v hv, c⁻¹, ?_⟩
    rw [pt_idxv v hv, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  -- the arc
  let τ : Fin (b + 1) → F := fun m => (Fintype.equivFin F).symm (Fin.castLE hb m)
  have hτ : Function.Injective τ := by
    intro m m' e
    exact Fin.castLE_injective hb ((Fintype.equivFin F).symm.injective e)
  let a := arc τ
  let idx : Fin (b + 2) → Fin S.card := fun m => idxv (a m) (arc_ne_zero τ m)
  have pt_idx : ∀ m, ∃ c : F, c ≠ 0 ∧ pt (idx m) = c • a m := by
    intro m
    obtain ⟨c, hc, h⟩ := nrm_eq (a m) (arc_ne_zero τ m)
    exact ⟨c, hc, by rw [pt_idxv _ (arc_ne_zero τ m), h]⟩
  have dot_idx : ∀ m (w : Fin 3 → F), (pt (idx m) ⬝ᵥ w = 0 ↔ a m ⬝ᵥ w = 0) := by
    intro m w
    obtain ⟨c, hc, h⟩ := pt_idx m
    rw [h, smul_dotProduct, smul_eq_mul, mul_eq_zero]
    simp [hc]
  have idx_inj : Function.Injective idx := by
    intro m m' e
    by_contra hne
    obtain ⟨c, hc, h⟩ := pt_idx m
    obtain ⟨c', hc', h'⟩ := pt_idx m'
    apply arc_nonprop hτ hne (c'⁻¹ * c)
    have : c' • a m' = c • a m := by rw [← h, ← h', e]
    rw [← smul_smul, ← this, smul_smul, inv_mul_cancel₀ hc', one_smul]
  -- the lines: one per pair of arc points
  let Pr : Finset (Finset (Fin (b + 2))) := (Finset.univ : Finset (Fin (b + 2))).powersetCard 2
  let eP := Pr.equivFin
  let sp : Fin Pr.card → Finset (Fin (b + 2)) := fun i => (eP.symm i : Finset (Fin (b + 2)))
  have sp_card : ∀ i, (sp i).card = 2 := fun i => (Finset.mem_powersetCard.mp (eP.symm i).2).2
  have sp_two : ∀ i, ∃ x y : Fin (b + 2), x ≠ y ∧ sp i = {x, y} :=
    fun i => Finset.card_eq_two.mp (sp_card i)
  choose e1 e2 he hsp using sp_two
  have mem_sp : ∀ i m, m ∈ sp i ↔ m = e1 i ∨ m = e2 i := by
    intro i m; rw [hsp i]; simp
  let l : Fin Pr.card → Fin 3 → F := fun i => crossProduct (a (e1 i)) (a (e2 i))
  have on_line : ∀ i m, m ∈ sp i → a m ⬝ᵥ l i = 0 := by
    intro i m hm
    rcases (mem_sp i m).mp hm with rfl | rfl
    · exact dot_self_cross _ _
    · exact dot_cross_self _ _
  have off_line : ∀ i m, m ∉ sp i → a m ⬝ᵥ l i ≠ 0 := by
    intro i m hm
    rw [mem_sp] at hm
    push Not at hm
    exact arc_tri hτ (e1 i) (e2 i) m (he i) (Ne.symm hm.1) (Ne.symm hm.2)
  have hl0 : ∀ i, l i ≠ 0 := by
    intro i
    apply crossProduct_ne_zero_iff_linearIndependent.mpr
    rw [LinearIndependent.pair_iff' (arc_ne_zero τ (e1 i))]
    intro c e
    exact arc_nonprop hτ (he i) c e.symm
  have hld : ∀ i j : Fin Pr.card, i ≠ j → ∀ c : F, l j ≠ c • l i := by
    intro i j hij c e
    have hs : sp i ≠ sp j := by
      intro h; apply hij; apply eP.symm.injective; exact Subtype.ext h
    have : ∃ m ∈ sp i, m ∉ sp j := by
      by_contra hc
      push Not at hc
      exact hs (Finset.eq_of_subset_of_card_le hc (by rw [sp_card, sp_card]))
    obtain ⟨m, hmi, hmj⟩ := this
    apply off_line j m hmj
    rw [e, dotProduct_smul, on_line i m hmi, smul_zero]
  let y : Fin Pr.card → Finset (Fin S.card) := fun i => ((Finset.univ \ sp i)).image idx
  have mem_y : ∀ i p, p ∈ y i ↔ ∃ m, m ∉ sp i ∧ idx m = p := by
    intro i p; simp [y]
  have hyc : ∀ i, (y i).card ≤ b := by
    intro i
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), sp_card, Finset.card_univ,
      Fintype.card_fin]
    omega
  have hyoff : ∀ i, ∀ p ∈ y i, pt p ⬝ᵥ l i ≠ 0 := by
    intro i p hp
    obtain ⟨m, hm, rfl⟩ := (mem_y i p).mp hp
    rw [Ne, dot_idx]
    exact off_line i m hm
  let g : (Fin S.card → Bool) → Bool := fun x =>
    decide (∀ j : Fin Pr.card, ∃ p, x p = true ∧ pt p ⬝ᵥ l j = 0)
  have hgmono : ∀ x x' : Fin S.card → Bool, (∀ v, x v = true → x' v = true) →
      g x = true → g x' = true := by
    intro x x' hxx' hx
    simp only [g, decide_eq_true_eq] at hx ⊢
    intro j
    obtain ⟨p, hp, hpj⟩ := hx j
    exact ⟨p, hxx' p hp, hpj⟩
  have hsafe : ∀ (i : Fin Pr.card) (x : Fin S.card → Bool), g x = true →
      ∃ p, x p = true ∧ pt p ⬝ᵥ l i = 0 := by
    intro i x hx
    simp only [g, decide_eq_true_eq] at hx
    exact hx i
  -- the set: arc minus one point of the line hits every line
  have hit : ∀ i (u w : Fin (b + 2)), u ∈ sp i → w ∈ sp i → u ≠ w →
      g (fun v => decide (v ∈ y i ∨ v = idx u)) = true := by
    intro i u w hu hw huw
    simp only [g, decide_eq_true_eq]
    intro j
    have : ∃ m ∈ sp j, m ≠ w := by
      by_cases h1 : e1 j = w
      · exact ⟨e2 j, (mem_sp j _).mpr (Or.inr rfl), fun h => he j (h1.trans h.symm)⟩
      · exact ⟨e1 j, (mem_sp j _).mpr (Or.inl rfl), h1⟩
    obtain ⟨m, hmj, hmw⟩ := this
    refine ⟨idx m, ?_, (dot_idx m _).mpr (on_line j m hmj)⟩
    by_cases hmi : m ∈ sp i
    · right
      rw [mem_sp] at hmi hu hw
      have : m = u := by
        rcases hmi with h | h <;> rcases hu with h' | h' <;> rcases hw with h'' | h'' <;>
          simp_all
      rw [this]
    · left
      exact (mem_y i _).mpr ⟨m, hmi, rfl⟩
  have htwo : ∀ i : Fin Pr.card, ∃ p p' : Fin S.card, p ≠ p' ∧ pt p ⬝ᵥ l i = 0 ∧
      pt p' ⬝ᵥ l i = 0 ∧ g (fun v => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v => decide (v ∈ y i ∨ v = p')) = true := by
    intro i
    have h1 : e1 i ∈ sp i := (mem_sp i _).mpr (Or.inl rfl)
    have h2 : e2 i ∈ sp i := (mem_sp i _).mpr (Or.inr rfl)
    refine ⟨idx (e1 i), idx (e2 i), fun h => he i (idx_inj h),
      (dot_idx _ _).mpr (on_line i _ h1), (dot_idx _ _).mpr (on_line i _ h2),
      hit i _ _ h1 h2 (he i), hit i _ _ h2 h1 (Ne.symm (he i))⟩
  have hk : 2 * Pr.card = (b + 1) * (b + 2) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, two_choose]
  exact ⟨S.card, Pr.card, pt, l, y, g, hpt0, hptd, hcov, hl0, hld, hyc, hyoff, hgmono, hsafe,
    htwo, hk⟩


end PEqualNP.Outside.L_meta_989

theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) :=
  ⟨PEqualNP.Outside.L_meta_989.part1_aux, PEqualNP.Outside.L_meta_989.part2_aux⟩
