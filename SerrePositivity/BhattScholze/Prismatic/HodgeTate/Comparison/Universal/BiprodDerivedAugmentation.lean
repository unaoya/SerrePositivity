module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.KFlatBiprodModels

/-!
# 元の二次数模型と標準非有界導来増大

## 概要
二本の元のsingleで計算した標準導来増大を、同じ直和の元の複体へ接続する。

## 方針
実際のK-flat模型の直和を使い、同じ増大の自然性で元の任意の分解へ戻す。

## 規約
非有界導来係数拡大の加法性を新しく仮定しない。元の複体そのもののK-flat性も要求しない。

## 使われ方
元のηの二次数の形式の直和に対する標準導来増大の同型性。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 同じK-flat増大の像が擬同型なら、元の標準導来増大は同型。 -/
theorem nativeDerivedAugmentation_isIso_of_model (f : A →+* B)
    {K L : Complex A} (q : K ⟶ L) (hq : QuasiIso q) (hK : complexKFlat A K)
    (hEq : QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q)) :
    IsIso ((complexDerivedExtensionAugmentation f).app L) := by
  haveI := hq
  haveI := hEq
  haveI := complexDerivedExtensionAugmentation_isIso f K hK
  have hn := (complexDerivedExtensionAugmentation f).naturality q
  change (complexDerivedExtension f).map (DerivedCategory.Q.map q) ≫
    (complexDerivedExtensionAugmentation f).app L =
    (complexDerivedExtensionAugmentation f).app K ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) at hn
  haveI : IsIso ((complexDerivedExtension f).map (DerivedCategory.Q.map q) ≫
      (complexDerivedExtensionAugmentation f).app L) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((complexDerivedExtension f).map (DerivedCategory.Q.map q)) _

/-- 元の標準導来増大が同型なら、同じ元の指定分解の係数拡大した増大は擬同型。 -/
theorem nativeResolutionAugmentation_baseChange_quasiIso (f : A →+* B) (K : Complex A)
    [IsIso ((complexDerivedExtensionAugmentation f).app K)] :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      ((complexResolutionAugmentation A).app K)) := by
  let q := (complexResolutionAugmentation A).app K
  haveI := complexResolutionAugmentation_quasiIso A K
  haveI := complexDerivedExtensionAugmentation_isIso f _ (complexResolutionFunctor_kFlat A K)
  have hn := (complexDerivedExtensionAugmentation f).naturality q
  change (complexDerivedExtension f).map (DerivedCategory.Q.map q) ≫
    (complexDerivedExtensionAugmentation f).app K =
    (complexDerivedExtensionAugmentation f).app ((complexResolutionFunctor A).obj K) ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) at hn
  haveI : IsIso ((complexDerivedExtensionAugmentation f).app ((complexResolutionFunctor A).obj K) ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q)) := by
    rw [← hn]
    infer_instance
  haveI : IsIso (DerivedCategory.Q.map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q)) :=
    IsIso.of_isIso_comp_left ((complexDerivedExtensionAugmentation f).app
      ((complexResolutionFunctor A).obj K)) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance

/-- 元の標準導来増大の同型性は、同じ二本の複体の直和へ移る。 -/
theorem nativeDerivedAugmentation_biprod_isIso (f : A →+* B) (K L : Complex A)
    [IsIso ((complexDerivedExtensionAugmentation f).app K)]
    [IsIso ((complexDerivedExtensionAugmentation f).app L)] :
    IsIso ((complexDerivedExtensionAugmentation f).app (K ⊞ L)) := by
  let qK := (complexResolutionAugmentation A).app K
  let qL := (complexResolutionAugmentation A).app L
  haveI := complexResolutionAugmentation_quasiIso A K
  haveI := complexResolutionAugmentation_quasiIso A L
  haveI := nativeResolutionAugmentation_baseChange_quasiIso f K
  haveI := nativeResolutionAugmentation_baseChange_quasiIso f L
  exact nativeDerivedAugmentation_isIso_of_model f (biprod.map qK qL)
    (quasiIso_biprod_map_model qK qL)
    (complexKFlat_biprod_model _ _ (complexResolutionFunctor_kFlat A K)
      (complexResolutionFunctor_kFlat A L))
    (mappedBiprod_quasiIso_model ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)) qK qL)

/-- 元の複体の指定同型は、同じ標準導来増大の同型性を保つ。 -/
theorem nativeDerivedAugmentation_isIso_of_iso (f : A →+* B) {K L : Complex A} (e : K ≅ L)
    [IsIso ((complexDerivedExtensionAugmentation f).app L)] :
    IsIso ((complexDerivedExtensionAugmentation f).app K) := by
  have hn := (complexDerivedExtensionAugmentation f).naturality e.hom
  haveI : IsIso ((complexDerivedExtensionAugmentation f).app K ≫
      (extension f ⋙ DerivedCategory.Q).map e.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((extension f ⋙ DerivedCategory.Q).map e.hom)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
