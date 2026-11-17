module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ResolvedOrdinaryComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ResolvedOrdinaryComparison

/-!
# 完備した元の増大による通常比較の同型性

## 概要
元の増大が完備した係数拡大で擬同型なら、同じ通常比較の成分は同型。

## 方針
元の完備した増大と、元の終域の標準完備化単位の逆を合成する。

## 規約
完備化前の増大の擬同型性は要求しない。元の複体の同型による移送も自然性で行う。

## 使われ方
元のTot模型への同型を経由し、元のHT全複体の指定増大へ戻す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonResolution HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) {s : ℕ} (y : Fin s → B)

/-- 同じ元の標準分解の完備した増大の擬同型性は、元の複体の同型で移せる。 -/
theorem completedResolutionAugmentation_quasiIso_of_iso {K L : Complex A} (e : K ≅ L)
    (hq : QuasiIso ((finiteCompletionFunctor y).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
        ((complexResolutionAugmentation A).app L)))) :
    QuasiIso ((finiteCompletionFunctor y).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
        ((complexResolutionAugmentation A).app K))) := by
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ finiteCompletionFunctor y
  let N := Functor.whiskerRight (complexResolutionAugmentation A) E
  have hn := congrArg DerivedCategory.Q.map (N.naturality e.hom)
  simp only [Functor.map_comp] at hn
  haveI := hq
  change DerivedCategory.Q.map ((complexResolutionFunctor A ⋙ E).map e.hom) ≫
      DerivedCategory.Q.map (N.app L) =
    DerivedCategory.Q.map (N.app K) ≫ DerivedCategory.Q.map (E.map e.hom) at hn
  haveI : IsIso (DerivedCategory.Q.map (N.app L)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  haveI : IsIso (DerivedCategory.Q.map (N.app K) ≫ DerivedCategory.Q.map (E.map e.hom)) := by
    rw [← hn]
    infer_instance
  haveI : IsIso (DerivedCategory.Q.map (N.app K)) := IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map (E.map e.hom))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ (N.app K)).mp inferInstance

variable {C : Type (u + 1)} [Category.{u} C] (F : C ⥤ Complex A)
variable (hF : ∀ K : C, ∀ j, IsComplete B (y j) (DerivedCategory.Q.obj
  (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj (F.obj K))))

/-- 完備した元の増大が擬同型なら、元の通常比較の同じ成分は同型。 -/
theorem resolvedOrdinaryComparison_app_isIso_of_completed (K : C)
    (hq : QuasiIso ((finiteCompletionFunctor y).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
        ((complexResolutionAugmentation A).app (F.obj K))))) :
    IsIso ((resolvedOrdinaryComparison f y F hF).app K) := by
  haveI : IsIso ((resolvedOrdinaryAugmentation f y F).app K) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  change IsIso ((resolvedOrdinaryAugmentation f y F).app K ≫
    (ordinaryTargetUnitIso f y F hF).inv.app K)
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
