module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverCompleteness
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeDerivedScalarModels
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationComparison

/-!
# Torが消える元の行への任意のK-flat増大の係数拡大

## 概要
元の離散行の高次Torが消えるとき、指定半自由模型から元の行への増大も係数拡大後に擬同型となる。

## 方針
元の上に有界な射影分解で標準導来増大を計算し、その自然性で任意のK-flat模型へ移す。

## 規約
係数環全体の平坦性や、指定半自由模型の上への有界性を要求しない。

## 使われ方
HT04.R1の標準の厳密な行射の擬同型性を元の行のTor消滅へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B]

/-- 高次Torが消える元の離散行では、元の非有界導来係数拡大の増大は同型。 -/
theorem nativeDerivedAugmentation_isIso_of_torVanishing (φ : R →+* B)
    (M : ModuleCat.{u} R) (hTor : scalarExtensionTorVanishing φ M) :
    IsIso ((complexDerivedExtensionAugmentation φ).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  let P := projectiveResolutionDerivedModel (projectiveResolution M)
  let ε := projectiveResolutionCochainAugmentation (projectiveResolution M)
  let E := (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)
  let s := (HomologicalComplex.singleMapHomologicalComplex
    (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M
  have hp : complexKFlat R P.complex :=
    complexKFlat_of_flat_boundedAbove R P.complex P.bound
      ((CochainComplex.isStrictlyLE_iff _ _).mp P.bounded)
      (fun i => by haveI := P.projective i; infer_instance)
  have hA : IsIso ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M) := by
    haveI := (derivedModuleBaseChangeAugmentation_isIso_iff φ M).mpr hTor
    change IsIso ((boundedAboveDerivedBaseChangeModuleNatIso φ).hom.app M ≫
      (derivedModuleBaseChangeAugmentation φ).app M)
    infer_instance
  have he := boundedAboveDerivedBaseChangeModuleAugmentation_projective_models φ P ε rfl
  haveI : IsIso ((boundedAboveDerivedBaseChangeModelIso φ
      (boundedAboveDerivedSingleFunctor.obj M) P).hom ≫ DerivedCategory.Q.map (E.map ε ≫ s)) :=
    he ▸ hA
  haveI : IsIso (DerivedCategory.Q.map (E.map ε ≫ s)) :=
    IsIso.of_isIso_comp_left
      (boundedAboveDerivedBaseChangeModelIso φ (boundedAboveDerivedSingleFunctor.obj M) P).hom _
  haveI : IsIso (DerivedCategory.Q.map (E.map ε) ≫ DerivedCategory.Q.map s) := by
    rw [← Functor.map_comp]
    infer_instance
  haveI : IsIso (DerivedCategory.Q.map (E.map ε)) :=
    IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map s)
  haveI := complexDerivedExtensionAugmentation_isIso φ P.complex hp
  have hn := (complexDerivedExtensionAugmentation φ).naturality ε
  change (complexDerivedExtension φ).map (DerivedCategory.Q.map ε) ≫
    (complexDerivedExtensionAugmentation φ).app ((CochainComplex.singleFunctor _ 0).obj M) =
    (complexDerivedExtensionAugmentation φ).app P.complex ≫ DerivedCategory.Q.map (E.map ε) at hn
  haveI : IsIso ((complexDerivedExtension φ).map (DerivedCategory.Q.map ε) ≫
      (complexDerivedExtensionAugmentation φ).app ((CochainComplex.singleFunctor _ 0).obj M)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((complexDerivedExtension φ).map (DerivedCategory.Q.map ε)) _

/-- 任意のK-flat模型から元のTor非輪状な離散行への増大は、係数拡大で擬同型を保つ。 -/
theorem baseChange_quasiIso_to_single_of_torVanishing (φ : R →+* B)
    (M : ModuleCat.{u} R) (hTor : scalarExtensionTorVanishing φ M)
    {K : Complex R} (q : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
    (hq : QuasiIso q) (hK : complexKFlat R K) :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q) := by
  haveI := hq
  haveI := nativeDerivedAugmentation_isIso_of_torVanishing φ M hTor
  haveI := complexDerivedExtensionAugmentation_isIso φ K hK
  have hn := (complexDerivedExtensionAugmentation φ).naturality q
  change (complexDerivedExtension φ).map (DerivedCategory.Q.map q) ≫
    (complexDerivedExtensionAugmentation φ).app ((CochainComplex.singleFunctor _ 0).obj M) =
    (complexDerivedExtensionAugmentation φ).app K ≫ DerivedCategory.Q.map
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q) at hn
  haveI : IsIso ((complexDerivedExtensionAugmentation φ).app K ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q)) := by
    rw [← hn]
    infer_instance
  haveI : IsIso (DerivedCategory.Q.map
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map q)) :=
    IsIso.of_isIso_comp_left ((complexDerivedExtensionAugmentation φ).app K) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
