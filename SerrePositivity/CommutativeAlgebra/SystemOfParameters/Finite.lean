module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.IntegralDimension
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # 有限な拡大によるパラメータ系の移り方

## 概要

局所環の有限な拡大 `A → D` で、`m_A` の像の根基は `m_D`（`radical_map_eq_maximalIdeal_of_finite`）。
したがって、次元が等しければ `A` のパラメータ系の像は `D` のパラメータ系
（`IsSystemOfParameters.map_finite`）。素イデアル `P` による商で、像の根基が極大イデアルなら
パラメータ系（`isSystemOfParameters_quotient_of_radical`）。パラメータ系の像は環準同型の行き先で
極大イデアルの元の根基に入る（`IsSystemOfParameters.map_mem_radical` など）。

## 方針

有限な拡大の閉ファイバー `D/m_A D` は Artin 環なので、その極大イデアルは冪零。

## 規約

`exists_finite_quotientAlgebra` はパラメータ系と独立な代数構造の補題で、利用者のためにここに置く。

## 使われ方

論文 Lemma 2.2 と §5 のパラメータの選択、CLMST の段の局所性と長さ、Cohen–Macaulay の長さ
（`LengthAlgebra/CohenMacaulay`）、局所コホモロジーの零化（`HomologicalAlgebra`）。
-/

@[expose] public noncomputable section

universe u v w

open IsLocalRing PrimeSpectrum

namespace SerrePositivity

section Finite

open IsLocalRing

/-- 有限局所代数への拡大は、極大イデアルを根基とするイデアルを保つ。 -/
lemma radical_map_eq_maximalIdeal_of_finite
    {A : Type u} [CommRing A] [IsLocalRing A]
    (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    [IsLocalHom (algebraMap A D)] (I : Ideal A) (hI : I.radical = maximalIdeal A) :
    (I.map (algebraMap A D)).radical = maximalIdeal D := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (maximalIdeal.isMaximal D).isPrime).mpr
    exact (Ideal.map_mono (Ideal.le_radical.trans_eq hI)).trans
      (map_maximalIdeal_le (algebraMap A D))
  · obtain ⟨n, hn⟩ := maximalIdeal_pow_le_map_of_finite D (R := A)
    have hm : (maximalIdeal A).map (algebraMap A D) ≤
        (I.map (algebraMap A D)).radical := by
      rw [← hI]
      exact Ideal.map_radical_le _
    intro z hz
    have : z ∈ ((I.map (algebraMap A D)).radical).radical :=
      Ideal.mem_radical_iff.mpr ⟨n, hm (hn (Ideal.pow_mem_pow hz n))⟩
    simpa only [Ideal.radical_idem] using this

/-- 単射な有限局所拡大では、パラメータ系の像もパラメータ系になる。 -/
theorem IsSystemOfParameters.map_finite
    {A : Type u} [CommRing A] [IsLocalRing A]
    (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) {h : ℕ} {z : Fin h → A}
    (hz : IsSystemOfParameters A z) :
    IsSystemOfParameters D (algebraMap A D ∘ z) := by
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  refine ⟨(ringKrullDim_eq_of_integral_of_injective A D hinj).trans hz.1, ?_⟩
  rw [Set.range_comp, ← Ideal.map_span]
  exact radical_map_eq_maximalIdeal_of_finite D _ hz.2

/-- `√(P + (x)) = m_R` と商の次元から、商環内のパラメータ系を得る。 -/
theorem isSystemOfParameters_quotient_of_radical
    {R : Type u} [CommRing R] [IsLocalRing R] (P : Ideal R) [IsLocalRing (R ⧸ P)]
    {h : ℕ} (x : Fin h → R) (hdim : ringKrullDim (R ⧸ P) = h)
    (hprimary : (P ⊔ Ideal.span (Set.range x)).radical = maximalIdeal R) :
    IsSystemOfParameters (R ⧸ P) (Ideal.Quotient.mk P ∘ x) := by
  refine ⟨hdim, ?_⟩
  have heq : (P ⊔ Ideal.span (Set.range x)).map (Ideal.Quotient.mk P) =
      Ideal.span (Set.range (Ideal.Quotient.mk P ∘ x)) := by
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, ← Set.range_comp]
  rw [← heq, ← Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact le_sup_left), hprimary]
  exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- `I ≤ Q` なら、`R/Q` 上有限な代数に両立する有限 `R/I` 代数構造を与えられる。 -/
theorem exists_finite_quotientAlgebra
    {R : Type u} [CommRing R] (I Q : Ideal R) (hIQ : I ≤ Q)
    (T : Type u) [CommRing T] [Algebra R T] [Algebra (R ⧸ Q) T]
    [IsScalarTower R (R ⧸ Q) T] [Module.Finite (R ⧸ Q) T] :
    ∃ (_ : Algebra (R ⧸ I) T), IsScalarTower R (R ⧸ I) T ∧ Module.Finite (R ⧸ I) T := by
  let f : R ⧸ I →+* T := Ideal.Quotient.lift I (algebraMap R T) fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ Q) T, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hIQ hr), map_zero]
  let : Algebra (R ⧸ I) T := f.toAlgebra
  let : IsScalarTower R (R ⧸ I) T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R T := Module.Finite.trans (R ⧸ Q) T
  exact ⟨inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite R _ _⟩

end Finite

section RadicalImage

variable {D : Type u} {C : Type v} [CommRing D] [CommRing C] [IsLocalRing D]

/-- A maximal-ideal element maps into the radical of every mapped parameter ideal. -/
lemma IsSystemOfParameters.map_mem_radical {r : ℕ} {y : Fin r → D}
    (hy : IsSystemOfParameters D y) (φ : D →+* C) {a : D}
    (ha : a ∈ IsLocalRing.maximalIdeal D) :
    φ a ∈ (Ideal.span (Set.range (φ ∘ y))).radical := by
  rw [← hy.2] at ha
  have h := Ideal.map_radical_le φ
    (Ideal.mem_map_of_mem φ ha)
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h

/-- The mapped coordinates of another parameter system have the required support. -/
lemma IsSystemOfParameters.map_coordinates_mem_radical {e r : ℕ} {z : Fin e → D}
    {y : Fin r → D} (hz : IsSystemOfParameters D z) (hy : IsSystemOfParameters D y)
    (φ : D →+* C) (j : Fin e) :
    φ (z j) ∈ (Ideal.span (Set.range (φ ∘ y))).radical := by
  apply hy.map_mem_radical φ
  rw [← hz.2]
  exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self j))

/-- Finite injective local extensions supply the support condition for any parameter system. -/
lemma IsSystemOfParameters.finite_map_coordinates_mem_radical
    {D E C : Type u} [CommRing D] [CommRing E] [CommRing C]
    [IsLocalRing D] [IsLocalRing E] [Algebra D E] [Module.Finite D E]
    (hinj : Function.Injective (algebraMap D E))
    {e r : ℕ} {z : Fin e → D} {y : Fin r → E}
    (hz : IsSystemOfParameters D z) (hy : IsSystemOfParameters E y)
    (φ : E →+* C) (j : Fin e) :
    φ (algebraMap D E (z j)) ∈ (Ideal.span (Set.range (φ ∘ y))).radical :=
  (hz.map_finite E hinj).map_coordinates_mem_radical hy φ j

end RadicalImage

/-- Noether 局所環 `A` 上有限な代数 `T` と、`√(z) = m_A` なる列 `z` について、`T/(z)T` は Artin 環。
`A/(z)` は（`m_A` 準素イデアルによる商なので）Artin 環（`isArtinianRing_quotient_of_le_radical`）で、
`T/(z)T` はその上の有限生成加群だから。`T` の局所性は要らない。 -/
lemma isArtinianRing_quotient_span_of_finite (A T : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T] [Algebra A T]
    [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (hz : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal A) :
    IsArtinianRing (T ⧸ Ideal.span (Set.range (algebraMap A T ∘ z))) := by
  let I := Ideal.span (Set.range z)
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : IsArtinianRing (A ⧸ I) :=
    isArtinianRing_quotient_of_le_radical (IsLocalRing.maximalIdeal A) I (by rw [hz])
  have : Module.Finite A (T ⧸ I.map (algebraMap A T)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (I.map (algebraMap A T))).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (A ⧸ I) (T ⧸ I.map (algebraMap A T)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hI : I.map (algebraMap A T) =
      Ideal.span (Set.range (algebraMap A T ∘ z)) := by
    dsimp only [I]
    rw [Ideal.map_span, Set.range_comp]
  rw [← hI]
  exact IsArtinianRing.of_finite (A ⧸ I) (T ⧸ I.map (algebraMap A T))

end SerrePositivity
