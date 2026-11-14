module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Definition
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Definition

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
public import SerrePositivity.BhattScholze.Prism.Basic.Bounded
import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-!
# 有界 prism の完全平坦な導来剰余

## 概要
完全平坦な導来対象の生成元冪による剰余は、離散で p 冪ねじれが有界。

## 方針
冪で零化される係数加群を有限に分解し、主元の完備な剰余に関する既存の純性定理を適用する。

## 規約
BS 著者版 Lemma 3.7 (2) の上に有界な導来対象の模型。

## 使われ方
有界 prism への完全平坦な射の構成。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private theorem pureFlat_of_all_model_tests (X : DerivedCategory.Minus (ModuleCat.{u} A))
    (P : BoundedAboveDerivedModel X.obj)
    (ht : ∀ (N : ModuleCat.{u} A) (i : ℤ), i ≠ 0 →
      IsZero (((moduleTensorCochainFunctor P.complex).obj N).homology i)) :
    (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj X.obj)) ∧
      Module.Flat A ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj) := by
  have hX (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj X.obj) := by
    have hP : ∀ j, Module.Flat A (P.complex.X j) := by
      intro j
      have := P.projective j
      infer_instance
    have hk := cochain_homology_isZero_of_nilpotentIdeal_tests
      (⊥ : Ideal A) ⟨1, by simp⟩ P.complex hP i (fun N _ ↦ ht N i hi)
    exact hk.of_iso ((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso P.iso.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app P.complex)
  refine ⟨hX, ?_⟩
  let hGE : X.obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr (fun i hi ↦ hX i (by omega))
  let hLE : X.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr (fun i hi ↦ hX i (by omega))
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X.obj
  let e : X ≅ boundedAboveDerivedSingleFunctor.obj H :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj 0)
  apply flat_of_completelyFlat_nilpotent (⊥ : Ideal A) ⟨1, by simp⟩ H
  intro N _ _ _
  apply (isConcentratedInDegreeZero_derivedTensor_iff H N).mpr
  intro n hn
  let N₀ := ModuleCat.of A N
  let et := DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensor.mapIso
    (Iso.prod (Iso.refl (boundedAboveDerivedSingleFunctor.obj N₀)) e))
  let em := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).mapIso
      (derivedTensorUnresolvedModuleModelIso N₀ X P) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (-(n : ℤ))).app
      ((moduleTensorCochainFunctor P.complex).obj N₀)
  have htX := (ht N₀ (-(n : ℤ)) (by omega)).of_iso em
  have htH :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).mapIso et).isZero_iff.mp htX
  have hz := ((boundedAboveDerivedTensorModuleTorNatIso N₀ n).app H).isZero_iff.mp htH
  have := ModuleCat.subsingleton_of_isZero hz
  exact (torModuleComm (R := A) n H N).injective.subsingleton

private theorem pureFlat_of_kills_power (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (hX : IsDerivedCompletelyFlat I X)
    (q : A →+* B) (n : ℕ) (hq : I ^ n ≤ RingHom.ker q) :
    let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
    (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj Y)) ∧
      Module.Flat B ((DerivedCategory.homologyFunctor (ModuleCat B) 0).obj Y) := by
  let P := boundedAboveDerivedChosenModel X
  have hP : ∀ j, Module.Flat A (P.complex.X j) := by
    intro j
    have : Module.Projective A (P.complex.X j) := inferInstance
    infer_instance
  apply pureFlat_of_all_model_tests _ (boundedAboveDerivedBaseChangeModel q X)
  intro N i hi
  let G := ModuleCat.restrictScalars q
  let K := (moduleTensorCochainFunctor (baseChange q P.complex)).obj N
  have hn : ∀ r ∈ I ^ n, ∀ x : G.obj N, r • x = 0 := by
    intro r hr x
    change q r • (show N from x) = 0
    rw [show q r = 0 from hq hr, zero_smul]
  have hz : IsZero (((moduleTensorCochainFunctor P.complex).obj (G.obj N)).homology i) :=
    moduleProperty_of_idealPower_annihilated I
      (fun M ↦ IsZero (((moduleTensorCochainFunctor P.complex).obj M).homology i))
      (fun M hM ↦ modelTensor_homology_isZero_of_flat_reduction I X hX.1 hX.2 M hM i hi)
      (moduleTensorCochain_homology_isZero_extension P.complex hP i) n (G.obj N) hn
  let ec : (G.mapHomologicalComplex (.up ℤ)).obj K ≅
      (moduleTensorCochainFunctor P.complex).obj (G.obj N) :=
    (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso q N) (.up ℤ)).app
      P.complex
  let eh : G.obj (K.homology i) ≅
      ((moduleTensorCochainFunctor P.complex).obj (G.obj N)).homology i :=
    ((K.sc i).mapHomologyIso G).symm ≪≫ (homologyFunctor (ModuleCat A) (.up ℤ) i).mapIso ec
  change IsZero (K.homology i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (G.obj (K.homology i))
  exact ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso eh)

variable {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

include hP in
private theorem generatorPowerBounded (n : ℕ) :
    let Q := A ⧸ Ideal.span {P.generator ^ n}
    ∃ N : ℕ, ∀ m : ℕ, ∀ x : Q, (p : Q) ^ m * x = 0 → (p : Q) ^ N * x = 0 := by
  obtain ⟨N, hN⟩ := hP
  have hN' : ∀ k : ℕ, ∀ x : A ⧸ Ideal.span {P.generator},
      (Ideal.Quotient.mk (Ideal.span {P.generator}) (p : A)) ^ k * x = 0 →
        (Ideal.Quotient.mk (Ideal.span {P.generator}) (p : A)) ^ N * x = 0 := by
    change ∀ k : ℕ, ∀ x : A ⧸ P.ideal,
      (Ideal.Quotient.mk P.ideal (p : A)) ^ k * x = 0 →
        (Ideal.Quotient.mk P.ideal (p : A)) ^ N * x = 0
    simpa only [map_natCast] using hN
  refine ⟨N * n, fun m x hx ↦ ?_⟩
  simpa only [map_natCast] using
    _root_.SerrePositivity.BhattScholze.regular_power_quotient_torsion_bound (p : A) P.generator P.generator_regular
      N hN' n m x (by simpa only [map_natCast] using hx)

include hP in
/-- 概要：完全平坦な対象の任意の生成元冪での導来剰余は離散で、p 冪ねじれが有界。
方針：p 剰余での純性と平坦性を、元の二元イデアルの冪により零化される加群から得る。
規約：BS 著者版 Lemma 3.7 (2) の上に有界な対象の剰余。
使われ方：元の対象の純性と prism の構成。 -/
theorem derivedGeneratorPowerReduction_pure_bounded
    (X : DerivedCategory.Minus (ModuleCat.{u} A))
    (hc : IsComplete A (p : A) X.obj)
    (hf : IsDerivedCompletelyFlat (Ideal.span {(p : A), P.generator}) X) (n : ℕ) :
    let Q := A ⧸ Ideal.span {P.generator ^ n}
    let q := Ideal.Quotient.mk (Ideal.span {P.generator ^ n})
    let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
    Y.IsGE 0 ∧ Y.IsLE 0 ∧
      ∃ N : ℕ, ∀ m : ℕ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y,
        (q (p : A)) ^ m • x = 0 → (q (p : A)) ^ N • x = 0 := by
  let J := Ideal.span {P.generator ^ n}
  let Q := A ⧸ J
  let q := Ideal.Quotient.mk J
  let a := q (p : A)
  let K := Ideal.span {a}
  let r := Ideal.Quotient.mk K
  let Y := (boundedAboveDerivedBaseChange q).obj X
  let I := Ideal.span {(p : A), P.generator}
  have hp : (r.comp q) (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton a))
  have hd : (r.comp q) P.generator ^ n = 0 := by
    rw [← map_pow, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (P.generator ^ n))),
      map_zero]
  have hmap : I.map (r.comp q) = Ideal.span {(r.comp q) P.generator} := by
    rw [Ideal.map_span, Set.image_pair, hp, Ideal.span_insert_zero]
  have hkill : I ^ n ≤ RingHom.ker (r.comp q) := by
    rw [RingHom.ker, ← Ideal.map_le_iff_le_comap, Ideal.map_pow, hmap, Ideal.span_singleton_pow, hd]
    simp
  obtain ⟨hPure, hFlat⟩ := pureFlat_of_kills_power I X hf (r.comp q) n hkill
  let e := baseChangeCompositeIso q r X
  have hY (i : ℤ) (hi : i ≠ 0) := (hPure i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat (Q ⧸ K)) i).mapIso e)
  have := hFlat
  have hYF := Module.Flat.of_linearEquiv
    ((DerivedCategory.homologyFunctor (ModuleCat (Q ⧸ K)) 0).mapIso e).toLinearEquiv
  have hcY : IsComplete Q a Y.obj :=
    derivedBaseChange_principal_isComplete A (p : A) (P.generator ^ n)
      ((show IsSMulRegular A P.generator from P.generator_regular).pow n) X hc
  have hb := generatorPowerBounded P hP n
  have ha : ∃ N : ℕ, ∀ m : ℕ, ∀ x : Q, a ^ m * x = 0 → a ^ N * x = 0 := by
    have he : a = (p : Q) := map_natCast q p
    rw [he]
    exact hb
  exact derived_pure_bounded_torsion_of_complete_flat_reduction a Y hY hYF ha hcY

end SerrePositivity.BhattScholze.Prismatic
