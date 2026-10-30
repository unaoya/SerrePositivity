module

public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Data.Int.Interval
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.FiniteSupport.Basic

/-! # 有限長の複体の Euler 標数

## 概要

有限長のホモロジーを持つ有界な複体について、ホモロジーの長さの交代和（Euler 標数）と、項の長さの
交代和が一致すること（Euler–Poincaré）、写像錐と長完全列での交代和の加法性を示す。

## 方針

各次数の短完全列 `0 → B → Z → H → 0`、`0 → Z → C → B[1] → 0` の長さの加法性と、有限台の交代和の
組み替え（`CategoryTheory/AlternatingSum`・`FiniteSupportBounds`）による。

## 規約

長さは自然数値（`lengthNat`）で扱い、整数値の交代和はキャストで得る。

## 使われ方

Koszul 複体の Euler 標数（`Koszul/FiniteLength`・`KoszulMultiplicity`）、完全複体の Euler 標数
（`PerfectComplex`）。
-/

@[expose] public noncomputable section

universe u v w

section HomologyLength

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- ホモロジーの長さの総和 `Σ_i ℓ(H^i(P))`（自然数値）。無限長の項は `toNat` で `0` と数える。
デヴィサージュの帰納法の指標として使う。 -/
noncomputable def homologyLengthSum (P : CochainComplex (ModuleCat.{u} R) ℤ) : ℕ :=
  ∑ᶠ i : ℤ, (Module.length R (P.homology i)).toNat

/-- 零対象の長さは `0` である（`toNat` をとっても `0`）。 -/
lemma length_toNat_eq_zero_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) :
    (Module.length R M).toNat = 0 := by
  have := ModuleCat.subsingleton_of_isZero h
  simp [Module.length_eq_zero]

/-- 有界な複体では、ホモロジーの長さが `0` でない次数は有限個しかない（範囲 `[a, b]` の外では項が
零なのでホモロジーも零）。`finsum` を通常の有限和として扱うための条件。 -/
lemma homologyLength_support_finite (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    (Function.support fun i ↦ (Module.length R (P.homology i)).toNat).Finite := by
  obtain ⟨a, b, hab⟩ := hP
  apply finiteSupport_of_bounded_zero _ a b
  intro i hi
  exact length_toNat_eq_zero_of_isZero (isZero_homology_of_isZero_X _ _ (hab i hi))

/-- ホモトピー同値な複体はホモロジーが同型なので、長さの総和は等しい。 -/
lemma homologyLengthSum_eq_of_homotopyEquiv {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : HomotopyEquiv P P') : homologyLengthSum P = homologyLengthSum P' := by
  unfold homologyLengthSum
  congr 1
  funext i
  rw [(h.toHomologyIso i).toLinearEquiv.length_eq]

/-- シフト `P⟦n⟧` のホモロジーは `P` のホモロジーを `n` だけずらしたもの（`H^i(P⟦n⟧) ≅ H^{n+i}(P)`）
なので、長さの総和は変わらない。添字を `i ↦ n + i` で取り直す。 -/
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
/-- `0` 次以上で写像錐のホモロジーは零。長完全列 `H^i(K) → H^i(Cone f) → H^{i + 1}(Q) = 0` から
`H^i(K) → H^i(Cone f)` は全射。`i > 0` では `H^i(K) = 0`。`i = 0` では `H^0(Q) → H^0(K)` が全射なので、
完全性から `H^0(K) → H^0(Cone f)` は零写像、全射かつ零なので `H^0(Cone f) = 0`。 -/
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
/-- `i ≤ -2` では `H^i(Cone f) ≅ H^{i + 1}(Q)` なので長さが等しい。長完全列
`H^i(K) = 0 → H^i(Cone f) → H^{i + 1}(Q) → H^{i + 1}(K) = 0`（`i, i + 1 ≠ 0`）による。 -/
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
/-- `i = -1` の長さの関係 `ℓ(H^0(Q)) = ℓ(H^{-1}(Cone f)) + ℓ(H^0(K))`。短完全列
`0 → H^{-1}(Cone f) → H^0(Q) → H^0(K) → 0`（左の単射性は `H^{-1}(K) = 0` から、右の全射性は `f` の
`H^0` が全射であることから）での長さの加法性。 -/
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
/-- **長さが 1 減る**：`ℓ(H^0(K)) = 1` なら `Σ ℓ(H(Cone f)) + 1 = Σ ℓ(H(Q))`。各次数の比較（上の三つの
補題）から `ℓ(H^i(Cone f)) + [i = -1] = ℓ(H^{i + 1}(Q))` が得られ、`i` について足し合わせて添字をずらす。
`Q` のホモロジーが有限長（`hQfin`）で `Q` が有界（`hQb`）であることは、`finsum` を通常の有限和として
扱うために使う。 -/
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

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限長な中央の項をもつ完全列では、その整数値の長さは前後の射の像の長さの和である。 -/
theorem lengthInt_eq_add_range {M N L : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (he : Function.Exact f g)
    (hn : IsFiniteLength R N) :
    ((Module.length R N).toNat : ℤ) = (Module.length R (LinearMap.range f)).toNat +
      (Module.length R (LinearMap.range g)).toNat := by
  exact_mod_cast lengthNat_eq_add_range f g he hn

/-- 自然数で添字づけた長完全列の長さの交代和。
`C₀` への射が全射で、切断の直上 `Cₙ₊₁` が零なら、中央の交代和は両側の交代和の和となる。
各長さを像の長さに分け、部分和の誤差が連結射の像の長さだけになることを帰納的に示す。 -/
theorem lengthEuler_longExact
    (A B C : ℕ → ModuleCat.{u} R)
    (α : ∀ i, A i →ₗ[R] B i) (β : ∀ i, B i →ₗ[R] C i)
    (δ : ∀ i, C (i + 1) →ₗ[R] A i)
    (hab : ∀ i, Function.Exact (α i) (β i))
    (hbd : ∀ i, Function.Exact (β (i + 1)) (δ i))
    (hda : ∀ i, Function.Exact (δ i) (α i)) (hb : Function.Surjective (β 0))
    (hA : ∀ i, IsFiniteLength R (A i)) (hB : ∀ i, IsFiniteLength R (B i))
    (hC : ∀ i, IsFiniteLength R (C i)) (n : ℕ)
    (hz : Subsingleton (C (n + 1))) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.length R (B i)).toNat) =
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.length R (A i)).toNat) +
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.length R (C i)).toNat) := by
  let a := fun i => ((Module.length R (LinearMap.range (α i))).toNat : ℤ)
  let b := fun i => ((Module.length R (LinearMap.range (β i))).toNat : ℤ)
  let d := fun i => ((Module.length R (LinearMap.range (δ i))).toNat : ℤ)
  have eA i : ((Module.length R (A i)).toNat : ℤ) = d i + a i :=
    lengthInt_eq_add_range _ _ (hda i) (hA i)
  have eB i : ((Module.length R (B i)).toNat : ℤ) = a i + b i :=
    lengthInt_eq_add_range _ _ (hab i) (hB i)
  have eC i : ((Module.length R (C (i + 1))).toNat : ℤ) = b (i + 1) + d i :=
    lengthInt_eq_add_range _ _ (hbd i) (hC (i + 1))
  have eC0 : ((Module.length R (C 0)).toNat : ℤ) = b 0 := by
    dsimp [b]
    rw [LinearMap.range_eq_top.mpr hb, Module.length_top]
  have hd : d n = 0 := by
    have : Subsingleton (LinearMap.range (δ n)) :=
      Function.Surjective.subsingleton (δ n).surjective_rangeRestrict
    simp [d, Module.length_eq_zero]
  exact alternatingSum_range_exact
    (fun i ↦ ((Module.length R (A i)).toNat : ℤ))
    (fun i ↦ ((Module.length R (B i)).toNat : ℤ))
    (fun i ↦ ((Module.length R (C i)).toNat : ℤ)) a b d eA eB eC eC0 n hd

/-- 各項が有限長で高次が零となる長完全列では、長さの交代有限和は加法的である。
三列の消滅次数を共通の上界にまとめて `finsum` を有限和に直し、切断版の定理を適用する。 -/
theorem lengthEuler_finsum_longExact
    (A B C : ℕ → ModuleCat.{u} R)
    (α : ∀ i, A i →ₗ[R] B i) (β : ∀ i, B i →ₗ[R] C i)
    (δ : ∀ i, C (i + 1) →ₗ[R] A i)
    (hab : ∀ i, Function.Exact (α i) (β i))
    (hbd : ∀ i, Function.Exact (β (i + 1)) (δ i))
    (hda : ∀ i, Function.Exact (δ i) (α i)) (hb : Function.Surjective (β 0))
    (hA : ∀ i, IsFiniteLength R (A i)) (hB : ∀ i, IsFiniteLength R (B i))
    (hC : ∀ i, IsFiniteLength R (C i))
    (zA : ∃ n, ∀ i, n < i → Subsingleton (A i))
    (zB : ∃ n, ∀ i, n < i → Subsingleton (B i))
    (zC : ∃ n, ∀ i, n < i → Subsingleton (C i)) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.length R (B i)).toNat) =
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.length R (A i)).toNat) +
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.length R (C i)).toNat) := by
  obtain ⟨a, ha⟩ := zA
  obtain ⟨b, hb'⟩ := zB
  obtain ⟨c, hc⟩ := zC
  let n := a + b + c
  have cut (X : ℕ → ModuleCat.{u} R) (hX : ∀ i, n < i → Subsingleton (X i)) :
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.length R (X i)).toNat) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.length R (X i)).toNat := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    have := hX i (by omega)
    exact hi (by simp [Module.length_eq_zero])
  rw [cut A (fun i hi => ha i (by dsimp [n] at hi; omega)),
    cut B (fun i hi => hb' i (by dsimp [n] at hi; omega)),
    cut C (fun i hi => hc i (by dsimp [n] at hi; omega))]
  exact lengthEuler_longExact A B C α β δ hab hbd hda hb hA hB hC n (hc _ (by dsimp [n]; omega))

end SerrePositivity

end HomologyLength

section ComplexEuler

namespace SerrePositivity.FiniteLengthComplexEuler

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The range inside cycles has the same length as the original incoming image. -/
theorem length_toCycles_range (S : ShortComplex (ModuleCat.{u} R)) :
    Module.length R S.moduleCatToCycles.range = Module.length R S.f.hom.range := by
  have h := S.moduleCatToCycles.quotKerEquivRange.length_eq
  have hk : S.moduleCatToCycles.ker = S.f.hom.ker := by
    ext x
    change S.moduleCatToCycles x = 0 ↔ S.f.hom x = 0
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  rw [hk, S.f.hom.quotKerEquivRange.length_eq] at h
  exact h.symm

/-- The middle length is homology length plus the two boundary image lengths. -/
theorem shortComplex_length_identity (S : ShortComplex (ModuleCat.{u} R))
    (hfinite : IsFiniteLength R S.X₂) :
    ((Module.length R S.X₂).toNat : ℝ) =
      ((Module.length R S.f.hom.range).toNat : ℝ) +
      ((Module.length R S.homology).toNat : ℝ) +
      ((Module.length R S.g.hom.range).toNat : ℝ) := by
  have hcy := lengthNat_add_of_exact S.moduleCatToCycles.range.subtype
    S.moduleCatToCycles.range.mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    (hfinite.of_injective S.g.hom.ker.injective_subtype)
  have hX := lengthNat_ker_add_range S.g.hom hfinite
  have hh := S.moduleCatHomologyIso.toLinearEquiv.length_eq
  change Module.length R S.homology =
    Module.length R (S.g.hom.ker ⧸ S.moduleCatToCycles.range) at hh
  rw [hcy, length_toCycles_range, ← hh] at hX
  exact_mod_cast hX

/-- Ordinary Euler characteristic is invariant under a quasi-isomorphism. -/
theorem chiOrd_eq_of_quasiIso {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) [QuasiIso f] : chiOrd P = chiOrd Q := by
  unfold chiOrd
  congr 1
  funext q
  rw [(isoOfQuasiIsoAt f q).toLinearEquiv.length_eq]

/-- A categorical zero module has length zero. -/
theorem length_eq_zero_of_isZero (M : ModuleCat.{u} R) (hM : IsZero M) :
    Module.length R M = 0 := by
  let : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  exact Module.length_eq_zero

/-- Euler–Poincaré: the alternating homology length of a bounded finite-length
complex is the alternating length of its terms. -/
theorem chiOrd_eq_alternating_term_lengths
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hfinite : ∀ q, IsFiniteLength R (P.X q)) :
    chiOrd P = ∑ᶠ q : ℤ,
      ((q.negOnePow : ℤ) : ℝ) * ((Module.length R (P.X q)).toNat : ℝ) := by
  obtain ⟨a, b, hab⟩ := hbounded
  let boundary := fun q : ℤ =>
    ((Module.length R (P.d q (q + 1)).hom.range).toNat : ℝ)
  let homology := fun q : ℤ => ((Module.length R (P.homology q)).toNat : ℝ)
  have hidentity (q : ℤ) : ((Module.length R (P.X q)).toNat : ℝ) =
      boundary (q - 1) + homology q + boundary q := by
    have h := shortComplex_length_identity (P.sc q) (hfinite q)
    change ((Module.length R (P.X q)).toNat : ℝ) =
      ((Module.length R (P.d ((ComplexShape.up ℤ).prev q) q).hom.range).toNat : ℝ) +
      ((Module.length R (P.homology q)).toNat : ℝ) +
      ((Module.length R (P.d q ((ComplexShape.up ℤ).next q)).hom.range).toNat : ℝ) at h
    rw [CochainComplex.prev, CochainComplex.next] at h
    dsimp only [boundary, homology]
    rw [show q - 1 + 1 = q by omega]
    exact h
  have hbfin : Function.HasFiniteSupport boundary := by
    apply finiteSupport_of_bounded_zero boundary a b
    intro q hq
    have hzero := length_eq_zero_of_isZero (P.X q) (hab q hq)
    have hle := Module.length_le_of_surjective (P.d q (q + 1)).hom.rangeRestrict
      (P.d q (q + 1)).hom.surjective_rangeRestrict
    rw [hzero] at hle
    have hz : Module.length R (P.d q (q + 1)).hom.range = 0 := le_antisymm hle bot_le
    simp only [boundary, hz, ENat.toNat_zero, Nat.cast_zero]
  have hhfin : Function.HasFiniteSupport homology := by
    apply finiteSupport_of_bounded_zero homology a b
    intro q hq
    have hz := length_eq_zero_of_isZero (P.homology q)
      (isZero_homology_of_isZero_X P q (hab q hq))
    simp only [homology, hz, ENat.toNat_zero, Nat.cast_zero]
  exact alternatingFinsum_eq_of_boundary
    (fun q ↦ ((Module.length R (P.X q)).toNat : ℝ)) homology boundary hbfin hhfin hidentity

end SerrePositivity.FiniteLengthComplexEuler

end ComplexEuler
