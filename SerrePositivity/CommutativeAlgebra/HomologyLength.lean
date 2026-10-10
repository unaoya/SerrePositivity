module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Data.Int.Interval

/-!
# 写像錐のホモロジーの長さ（Lemma 3.5b の準備、段階 3 の後半）

ホモロジーの長さの総和 `homologyLengthSum P = Σ_i length H^i(P)` を定義し、次を示す。

- シフトとホモトピー同値で変わらない。
- `Q` が `1` 次以上で零、`K` のホモロジーが `0` 次に集中し `length H^0(K) = 1`、
  `f : Q → K` が `H^0` で全射なら、`Σ length H(Cone f) + 1 = Σ length H(Q)`。

後者がデヴィサージュで長さを 1 ずつ減らす一歩になる。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- ホモロジーの長さの総和（無限長の項は `0` と数える）。 -/
noncomputable def homologyLengthSum (P : CochainComplex (ModuleCat.{u} R) ℤ) : ℕ :=
  ∑ᶠ i : ℤ, (Module.length R (P.homology i)).toNat

/-- 零対象である加群の長さを自然数に移すと零になる。 -/
lemma length_toNat_eq_zero_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) :
    (Module.length R M).toNat = 0 := by
  have := ModuleCat.subsingleton_of_isZero h
  simp [Module.length_eq_zero]

/-- 有界な複体のホモロジーの長さは有限個の次数でしか `0` でない。 -/
lemma homologyLength_support_finite (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    (Function.support fun i ↦ (Module.length R (P.homology i)).toNat).Finite := by
  obtain ⟨a, b, hab⟩ := hP
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  exact hi (length_toNat_eq_zero_of_isZero
    (isZero_homology_of_isZero_X _ _ (hab i (by simp only [Set.mem_Icc] at hn; omega))))

/-- ホモトピー同値で長さの総和は変わらない。 -/
lemma homologyLengthSum_eq_of_homotopyEquiv {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : HomotopyEquiv P P') : homologyLengthSum P = homologyLengthSum P' := by
  unfold homologyLengthSum
  congr 1
  funext i
  rw [(h.toHomologyIso i).toLinearEquiv.length_eq]

/-- シフトで長さの総和は変わらない。 -/
lemma homologyLengthSum_shift (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    homologyLengthSum (P⟦n⟧) = homologyLengthSum P := by
  unfold homologyLengthSum
  have h : ∀ i : ℤ, (Module.length R ((P⟦n⟧).homology i)).toNat =
      (Module.length R (P.homology (n + i))).toNat := fun i ↦ by
    have e : (P⟦n⟧).homology i ≅ P.homology (n + i) :=
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) n i (n + i) rfl).app P
    rw [e.toLinearEquiv.length_eq]
  simp_rw [h]
  exact finsum_comp_equiv (Equiv.addLeft n) (f := fun i ↦ (Module.length R (P.homology i)).toNat)

/-! ## 写像錐 -/

section cone

variable {Q K : CochainComplex (ModuleCat.{u} R) ℤ} (f : Q ⟶ K)

/-- 写像錐の連結写像の後に元の写像のホモロジー写像が続く列の完全性を、線形写像の言葉に移す。 -/
private lemma fexact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact (Cone.δ f n₀ n₁ h).hom (HomologicalComplex.homologyMap f n₁).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (Cone.exact₁ f n₀ n₁ h)

/-- 元の写像と写像錐への包含が誘導するホモロジーの列の完全性を、線形写像の言葉に移す。 -/
private lemma fexact₂ (n : ℤ) :
    Function.Exact (HomologicalComplex.homologyMap f n).hom
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (Cone.exact₂ f n)

/-- 写像錐への包含の後に連結写像が続く列の完全性を、線形写像の言葉に移す。 -/
private lemma fexact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Function.Exact (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n₀).hom
      (Cone.δ f n₀ n₁ h).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (Cone.exact₃ f n₀ n₁ h)

variable (hQ : ∀ i : ℤ, 0 < i → IsZero (Q.X i)) (hK : ∀ i : ℤ, i ≠ 0 → IsZero (K.homology i))
  (hf : Function.Surjective (HomologicalComplex.homologyMap f 0).hom)

include hQ hK hf in
/-- `0` 次以上で写像錐のホモロジーは零。 -/
lemma isZero_mappingCone_homology_of_nonneg (i : ℤ) (hi : 0 ≤ i) :
    IsZero ((CochainComplex.mappingCone f).homology i) := by
  have hQ1 : IsZero (Q.homology (i + 1)) := isZero_homology_of_isZero_X _ _ (hQ _ (by omega))
  have := ModuleCat.subsingleton_of_isZero hQ1
  rw [ModuleCat.isZero_iff_subsingleton]
  -- `H^i(K) → H^i(Cone)` は全射
  have hsurj :=
    (LinearMap.surjective_iff_eq_zero_of_exact (fexact₃ f i (i + 1) rfl)).mpr
      (Subsingleton.elim _ _)
  rcases hi.lt_or_eq with hi | rfl
  · have := ModuleCat.subsingleton_of_isZero (hK i hi.ne')
    exact hsurj.subsingleton
  · -- `H^0(Q) → H^0(K)` が全射なので `H^0(K) → H^0(Cone)` は零
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [(fexact₂ f 0).apply_apply_eq_zero, (fexact₂ f 0).apply_apply_eq_zero]

include hK in
/-- `i ≤ -2` で `H^i(Cone) ≅ H^{i+1}(Q)`。 -/
lemma length_mappingCone_homology_of_le (i : ℤ) (hi : i ≤ -2) :
    Module.length R ((CochainComplex.mappingCone f).homology i) =
      Module.length R (Q.homology (i + 1)) := by
  have h1 := ModuleCat.subsingleton_of_isZero (hK i (by omega))
  have h2 := ModuleCat.subsingleton_of_isZero (hK (i + 1) (by omega))
  have hinj :=
    (LinearMap.injective_iff_eq_zero_of_exact (fexact₃ f i (i + 1) rfl)).mpr
      (Subsingleton.elim _ _)
  have hsurj :=
    (LinearMap.surjective_iff_eq_zero_of_exact (fexact₁ f i (i + 1) rfl)).mpr
      (Subsingleton.elim _ _)
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).length_eq

include hK hf in
/-- `H^{-1}(Cone) → H^0(Q) → H^0(K) → 0` から長さの関係。 -/
lemma length_mappingCone_homology_neg_one :
    Module.length R (Q.homology 0) =
      Module.length R ((CochainComplex.mappingCone f).homology (-1)) +
        Module.length R (K.homology 0) := by
  have h1 := ModuleCat.subsingleton_of_isZero (hK (-1) (by omega))
  have hinj :=
    (LinearMap.injective_iff_eq_zero_of_exact (fexact₃ f (-1) 0 (by omega))).mpr
      (Subsingleton.elim _ _)
  exact Module.length_eq_add_of_exact _ _ hinj hf (fexact₁ f (-1) 0 (by omega))

include hQ hK hf in
/-- **長さが 1 減る**：`length H^0(K) = 1` なら `Σ length H(Cone f) + 1 = Σ length H(Q)`。 -/
theorem homologyLengthSum_mappingCone (hK0 : Module.length R (K.homology 0) = 1)
    (hQfin : ∀ i, Module.length R (Q.homology i) ≠ ⊤)
    (hQb : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i)) :
    homologyLengthSum (CochainComplex.mappingCone f) + 1 = homologyLengthSum Q := by
  set Lc := fun i : ℤ ↦ (Module.length R ((CochainComplex.mappingCone f).homology i)).toNat
  set LQ := fun i : ℤ ↦ (Module.length R (Q.homology i)).toNat
  have key : ∀ i, Lc i + (if i = -1 then 1 else 0) = LQ (i + 1) := by
    intro i
    by_cases hi : 0 ≤ i
    · simp only [show i ≠ -1 by omega, ↓reduceIte, add_zero, Lc, LQ]
      rw [length_toNat_eq_zero_of_isZero (isZero_mappingCone_homology_of_nonneg f hQ hK hf i hi),
        length_toNat_eq_zero_of_isZero (isZero_homology_of_isZero_X _ _ (hQ _ (by omega)))]
    · by_cases hi' : i = -1
      · subst hi'
        simp only [↓reduceIte, Lc, LQ]
        rw [show (-1 : ℤ) + 1 = 0 by norm_num, length_mappingCone_homology_neg_one f hK hf, hK0]
        have hne : Module.length R ((CochainComplex.mappingCone f).homology (-1)) ≠ ⊤ := by
          intro htop
          have := hQfin 0
          rw [length_mappingCone_homology_neg_one f hK hf, htop] at this
          exact this (top_add _)
        rw [ENat.toNat_add hne (by simp)]
        rfl
      · simp only [hi', ↓reduceIte, add_zero, Lc, LQ]
        rw [length_mappingCone_homology_of_le f hK i (by omega)]
  have hQs : (Function.support LQ).Finite := homologyLength_support_finite Q hQb
  have hQs' : (Function.support fun i : ℤ ↦ LQ (i + 1)).Finite :=
    hQs.preimage (Equiv.addRight (1 : ℤ)).injective.injOn
  have hIs : (Function.support fun i : ℤ ↦ if i = -1 then (1 : ℕ) else 0).Finite :=
    (Set.finite_singleton (-1 : ℤ)).subset (fun i hi ↦ by
      by_contra h
      exact hi (by simp only [Set.mem_singleton_iff] at h; simp [h]))
  have hcs : (Function.support Lc).Finite := by
    apply hQs'.subset
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    rw [← key i]
    omega
  have hsum := finsum_add_distrib hcs hIs
  simp_rw [key] at hsum
  have h1 : ∑ᶠ i : ℤ, (if i = -1 then (1 : ℕ) else 0) = 1 := by
    rw [finsum_eq_single _ (-1 : ℤ) (fun i hi ↦ by simp [hi])]
    simp
  rw [h1] at hsum
  unfold homologyLengthSum
  change ∑ᶠ i, Lc i + 1 = ∑ᶠ i, LQ i
  rw [← hsum]
  exact finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := LQ)

end cone

end SerrePositivity
