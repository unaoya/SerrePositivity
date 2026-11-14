module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatDiscrete
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteCochainPurity
import all SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# 有界 prism 上の完全平坦な複体

## 概要
導来完備で完全平坦な対象の離散性を、次数に上界のない K-flat 複体で示す。

## 方針
生成元での剰余を先に調べる。平坦複体の主元簡約と Milnor 列で剰余を離散にし、
導来完備性で元の複体の離散性を得る。その後に上に有界な模型を使う。

## 規約
BS 著者版 Lemma 3.7 (2)。完全平坦性は (p,d) で零化される加群とのテンソルの離散性。

## 使われ方
導来完備な完全平坦対象の古典的完備性と、生成元冪商の有界ねじれ。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCompletion DifferentialGraded
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

private theorem modelTensor_purity_of_comparison
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : complexKFlat A K)
    (M : BoundedAboveDerivedModel (DerivedCategory.Q.obj K))
    (N : ModuleCat.{u} A) (i : ℤ)
    (hz : IsZero (((moduleTensorCochainFunctor K).obj N).homology i)) :
    IsZero (((moduleTensorCochainFunctor M.complex).obj N).homology i) := by
  obtain ⟨f, hf⟩ := exists_cochainMap_of_isKProjective M.iso.hom
  have : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) f).mp
    (hf ▸ inferInstanceAs (IsIso M.iso.hom))
  let R := projectiveResolutionDerivedModel (projectiveResolution N)
  let ε := projectiveResolutionCochainAugmentation (projectiveResolution N)
  have hflat (L : BoundedAboveDerivedModel (C := ModuleCat.{u} A) (DerivedCategory.Q.obj K))
      (j : ℤ) : Module.Flat A (L.complex.X j) := by
    have : Module.Projective A (L.complex.X j) := inferInstance
    infer_instance
  have hM := complexKFlat_of_flat_boundedAbove A M.complex M.bound
    ((CochainComplex.isStrictlyLE_iff _ _).mp M.bounded) (hflat M)
  have hR := complexKFlat_of_flat_boundedAbove A R.complex R.bound
    ((CochainComplex.isStrictlyLE_iff _ _).mp R.bounded) (fun j ↦ by
      have : Module.Projective A (R.complex.X j) := inferInstance
      infer_instance)
  have h₁ := complexKFlat_quasiIso_left A hM ε
  have h₂ := complexKFlat_quasiIso_right A hR f
  have h₃ := complexKFlat_quasiIso_left A hK ε
  let e := DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso N M.complex).symm ≪≫
    (asIso (DerivedCategory.Q.map (cochainTensorMap ε (𝟙 M.complex)))).symm ≪≫
    asIso (DerivedCategory.Q.map (cochainTensorMap (𝟙 R.complex) f)) ≪≫
    asIso (DerivedCategory.Q.map (cochainTensorMap ε (𝟙 K))) ≪≫
    DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso N K)
  exact hz.of_iso (((DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app _)

private theorem cochain_prism_pure
    {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : ∀ i, Module.Flat A (K.X i))
    (hp : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hd : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (ht : ∀ (N : ModuleCat.{u} A),
      (∀ r ∈ Ideal.span {(p : A), P.generator}, ∀ x : N, r • x = 0) →
      ∀ i : ℤ, i ≠ 0 → IsZero (((moduleTensorCochainFunctor K).obj N).homology i)) :
    (DerivedCategory.Q.obj K).IsGE 0 ∧ (DerivedCategory.Q.obj K).IsLE 0 := by
  let d := P.generator
  let d₁ := d ^ (1 : ℕ)
  let J := Ideal.span {d₁}
  let B := A ⧸ J
  let q := Ideal.Quotient.mk J
  let := q.toAlgebra
  let a := q (p : A)
  let L := baseChange q K
  let F := ModuleCat.restrictScalars q
  have hFL : ∀ j, Module.Flat B (L.X j) := by
    intro j
    let := hK j
    change Module.Flat B (B ⊗[A] (K.X j))
    infer_instance
  have hm : Mono (smulId d₁ K) := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    let := hK i
    apply (ModuleCat.mono_iff_injective _).mpr
    have hr : IsSMulRegular A d := P.generator_regular
    have hl : IsSMulRegular A d₁ := hr.pow 1
    have hr' : IsRegular d₁ := ⟨hl, fun x y h ↦ hl (by
      change d₁ * x = d₁ * y
      simpa only [mul_comm d₁] using h)⟩
    exact (show IsSMulRegular (K.X i) d₁ from Module.Flat.isSMulRegular_of_isRegular hr')
  let e₁ := koszulPowerCokernelAugmentation d K 1
  have he₁ : QuasiIso e₁ := CochainComplex.mappingCone.quasiIso_descShortComplex
    { exact := ShortComplex.exact_cokernel _, mono_f := hm, epi_g := inferInstance }
  let e₂ := powerCokernelTensorModelIso d K hK 1
  let e₃ : (F.mapHomologicalComplex (.up ℤ)).obj L ≅
      (moduleTensorCochainFunctor K).obj (ModuleCat.of A B) :=
    (F.mapHomologicalComplex (.up ℤ)).mapIso (moduleTensorCochainUnitIso L).symm ≪≫
      (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso q (ModuleCat.of B B))
        (.up ℤ)).app K
  let e : (derivedScalarConeFunctor A d₁).obj (DerivedCategory.Q.obj K) ≅
      (derivedRestrictScalars q).obj (DerivedCategory.Q.obj L) :=
    (derivedScalarConeComparison A d₁).app K ≪≫ asIso (DerivedCategory.Q.map e₁) ≪≫
      DerivedCategory.Q.mapIso (e₂ ≪≫ e₃.symm) ≪≫
      ((derivedRestrictScalarsFactors q).app L).symm
  have hpL : IsComplete B a (DerivedCategory.Q.obj L) :=
    (derivedRestrictScalars_isComplete_iff q (p : A) _).mp
      (isComplete_of_iso A (p : A) e (derivedScalarCone_isComplete A (p : A) d₁ _ hp))
  let I := Ideal.span {(p : A), d}
  have htL (n : ℕ) (N : ModuleCat.{u} B) (hN : ∀ x : N, a ^ n • x = 0)
      (i : ℤ) (hi : i ≠ 0) :
      IsZero (((moduleTensorCochainFunctor L).obj N).homology i) := by
    have hqd : q d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (by
        have h : d₁ = d := pow_one _
        rw [← h]
        exact Ideal.mem_span_singleton_self _)
    have hmap : I.map q = Ideal.span {a} := by
      rw [Ideal.map_span, Set.image_pair, hqd, Set.pair_comm, Ideal.span_insert_zero]
    have hann : ∀ r ∈ I ^ n, ∀ x : F.obj N, r • x = 0 := by
      intro r hr x
      have hr' := Ideal.mem_map_of_mem q hr
      rw [Ideal.map_pow, hmap, Ideal.span_singleton_pow] at hr'
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hr'
      change q r • (show N from x) = 0
      rw [hb, mul_comm, mul_smul, hN, smul_zero]
    have hz := moduleProperty_of_idealPower_annihilated I
      (fun M ↦ IsZero (((moduleTensorCochainFunctor K).obj M).homology i))
      (fun M hM ↦ ht M hM i hi) (moduleTensorCochain_homology_isZero_extension K hK i)
      n (F.obj N) hann
    let T := (moduleTensorCochainFunctor L).obj N
    let ec : (F.mapHomologicalComplex (.up ℤ)).obj T ≅
        (moduleTensorCochainFunctor K).obj (F.obj N) :=
      (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso q N) (.up ℤ)).app K
    let eh := ((T.sc i).mapHomologyIso F).symm ≪≫
      (homologyFunctor (ModuleCat A) (.up ℤ) i).mapIso ec
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (F.obj (T.homology i))
    exact ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso eh)
  obtain ⟨N, hN⟩ := generatorPowerBounded P hP 1
  have hBN : ∀ n : ℕ, ∀ x : B, a ^ n * x = 0 → a ^ N * x = 0 := by
    have he : a = (p : B) := map_natCast q p
    rw [he]
    exact hN
  have hzero (i : ℤ) (hi : i ≠ 0) :=
    isZero_homology_of_complete_of_powerTorsion_tests a L hFL hpL N hBN htL i hi
  have hcone (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        ((derivedScalarConeFunctor A d₁).obj (DerivedCategory.Q.obj K))) :=
    (F.map_isZero (hzero i hi)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso e ≪≫
        (derivedRestrictScalarsHomologyIso q i).app _ ≪≫
        F.mapIso ((DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app L))
  have hd₁ : IsComplete A d₁ (DerivedCategory.Q.obj K) := by
    simpa only [d₁, pow_one] using hd
  exact ⟨(derived_pure_of_complete_scalarCone_pure d₁ _ hd₁ hcone).1,
    (derived_pure_of_complete_scalarCone_pure d₁ _ hd₁ hcone).2.1⟩

/-- 概要：有界 prism 上の導来完備な完全平坦対象は離散で、H⁰ は古典的に完備で生成元が正則。
生成元冪での H⁰ の商は p 冪ねじれが有界。
方針：先に非有界の模型で離散性を示し、生成元冪の剰余と完備性には上に有界な結果を用いる。
規約：BS 著者版 Lemma 3.7 (2) の K-flat 複体による形。複体の次数に上界は不要。
使われ方：完全平坦な完備底変換の古典化。 -/
theorem completelyFlatCochain_isDiscrete_of_boundedPrism
    {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : ∀ i, Module.Flat A (K.X i))
    (hKF : complexKFlat A K)
    (hp : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hd : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (ht : ∀ (N : ModuleCat.{u} A),
      (∀ r ∈ Ideal.span {(p : A), P.generator}, ∀ x : N, r • x = 0) →
      ∀ i : ℤ, i ≠ 0 → IsZero (((moduleTensorCochainFunctor K).obj N).homology i)) :
    let X := DerivedCategory.Q.obj K
    let H := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X
    X.IsGE 0 ∧ X.IsLE 0 ∧ IsAdicComplete (Ideal.span {(p : A), P.generator}) H ∧
      (∀ n : ℕ, IsSMulRegular H (P.generator ^ n)) ∧
      ∀ n : ℕ, ∃ N : ℕ, ∀ (k : ℕ) (x : H ⧸ (Ideal.span {P.generator ^ n} • ⊤ : Submodule A H)),
        (p : A) ^ k • x = 0 → (p : A) ^ N • x = 0 := by
  let X : DerivedCategory.Minus (ModuleCat.{u} A) :=
    ⟨DerivedCategory.Q.obj K, ⟨0, (cochain_prism_pure P hP K hK hp hd ht).2⟩⟩
  let I := Ideal.span {(p : A), P.generator}
  let q := Ideal.Quotient.mk I
  let F := ModuleCat.restrictScalars q
  let M := boundedAboveDerivedChosenModel X
  have hf : IsDerivedCompletelyFlat I X := by
    unfold IsDerivedCompletelyFlat
    apply pureFlat_of_all_model_tests _ (boundedAboveDerivedBaseChangeModel q X)
    intro N i hi
    have hann (r : A) (hr : r ∈ I) (x : F.obj N) : r • x = 0 := by
      change q r • (show N from x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
    have hz := modelTensor_purity_of_comparison K hKF M (F.obj N) i (ht _ hann i hi)
    let T := (moduleTensorCochainFunctor (baseChange q M.complex)).obj N
    let ec : (F.mapHomologicalComplex (.up ℤ)).obj T ≅
        (moduleTensorCochainFunctor M.complex).obj (F.obj N) :=
      (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso q N) (.up ℤ)).app
        M.complex
    let eh := ((T.sc i).mapHomologyIso F).symm ≪≫
      (homologyFunctor (ModuleCat A) (.up ℤ) i).mapIso ec
    change IsZero (T.homology i)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (F.obj (T.homology i))
    exact ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso eh)
  exact derivedCompletelyFlat_isDiscrete_of_boundedPrism P hP X hp hd hf

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.7" (partial := special) "(1) と (2)（完全平坦な複体の離散性、通常の導来圏で、BS-W15 K4）、(3)（完全平坦な δ 代数から有界 prism、exists_boundedPrism_of_completelyFlat_deltaAlgebra）は本体。(4) は不要（D19）。向き付きの基底 ／ 11-11 更新（2） ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.completelyFlatCochain_isDiscrete_of_boundedPrism
