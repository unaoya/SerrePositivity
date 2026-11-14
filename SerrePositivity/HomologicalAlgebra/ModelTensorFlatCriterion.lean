module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedFlatModelTensor
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion

/-! # Tensor tests on a fixed model detect actual derived purity and flat H0 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- All coefficient tests on any projective model imply purity and flatness
of the original actual homology module. -/
theorem derived_pure_flat_of_modelTensor_tests
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj)
    (hAll : ∀ N : ModuleCat.{u} R, ∀ i : ℤ, i ≠ 0 →
      IsZero (((moduleTensorCochainFunctor P.complex).obj N).homology i)) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj) := by
  have hX (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X.obj) := by
    have hk := ((homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso
      (moduleTensorCochainUnitIso P.complex)).isZero_iff.mp (hAll (ModuleCat.of R R) i hi)
    exact hk.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso P.iso.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P.complex)
  let hGE : X.obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr
    (fun i hi ↦ hX i (by omega))
  let hLE : X.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr
    (fun i hi ↦ hX i (by omega))
  refine ⟨hGE, hLE, ?_⟩
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj
  let e : X ≅ boundedAboveDerivedSingleFunctor.obj H :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj 0)
  apply flat_of_completelyFlat_nilpotent (⊥ : Ideal R) ⟨1, by simp⟩ H
  intro N _ _ _
  apply (isConcentratedInDegreeZero_derivedTensor_iff H N).mpr
  intro n hn
  let N0 := ModuleCat.of R N
  let et := DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensor.mapIso
    (Iso.prod (Iso.refl (boundedAboveDerivedSingleFunctor.obj N0)) e))
  let em := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).mapIso
      (derivedTensorUnresolvedModuleModelIso N0 X P) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-(n : ℤ))).app
      ((moduleTensorCochainFunctor P.complex).obj N0)
  have htX := (hAll N0 (-(n : ℤ)) (by omega)).of_iso em
  have htH :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).mapIso et).isZero_iff.mp htX
  have hz := ((boundedAboveDerivedTensorModuleTorNatIso N0 n).app H).isZero_iff.mp htH
  have := ModuleCat.subsingleton_of_isZero hz
  exact (torModuleComm (R := R) n H N).injective.subsingleton

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.2.12" (partial := special) "仮定：通常の可換環 R と有界上導来対象、指定した射影模型（Lean が強い：通常環のこの導来模型の場合）。結論：全離散係数との模型テンソルが零次以外で消える条件から対象の離散性と H⁰ の平坦性を示し、逆に離散かつ平坦な H⁰ から同じ模型での消滅を示す（離散環上の平坦性のテンソル検査の部分に一致）。一般の環スペクトルの flat 述語との比較は含まれない。"] _root_.SerrePositivity.derived_pure_flat_of_modelTensor_tests
attribute [cite HA "7.2.2.15" (partial := direction) "仮定：通常可換環上の有界上導来対象と、その射影模型の全離散係数によるテンソルの零次集中（Lean が強い：この通常の導来模型の場合）。結論：対象が離散で H⁰ が平坦となる（(5)⇒(3) の離散環の場合に対応する部分に一致）。有限自由加群の filtered 余極限による Lazard 表示と五条件全体の同値は含まれない。"] _root_.SerrePositivity.derived_pure_flat_of_modelTensor_tests
attribute [cite HA "7.2.4.22" (partial := direction) "仮定：通常可換環の有界上導来対象と全離散係数との指定模型テンソルの零次集中（Lean が強い：この通常の導来模型の場合）。結論：対象が離散かつ H⁰ が平坦となる（amplitude 零のテンソル検査からの平坦性の方向に一致）。一般の連結環スペクトルにおける両方向の同値は含まれない。"] _root_.SerrePositivity.derived_pure_flat_of_modelTensor_tests
