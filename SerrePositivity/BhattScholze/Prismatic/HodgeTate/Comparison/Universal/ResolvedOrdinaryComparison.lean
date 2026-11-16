module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ComplexResolutionFunctor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent

/-!
# 同じ指定分解から通常係数拡大への標準完備比較

## 概要
通常係数拡大が指定した座標で完備な場合、元の指定分解と標準完備化単位から自然な比較を作る。

## 方針
指定増大の自然性と完備化単位の自然性を合成し、同じ元の単位との合成で比較を規格化する。

## 規約
元の分解の増大が係数拡大で擬同型となることは、同型性の判定時だけ適用側で与える。

## 使われ方
具体的な被覆の構成を展開せず、元のηの比較図式と標準単位の照合を行う。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonResolution HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]
variable {C : Type (u+1)} [Category.{u} C]
variable (f : A →+* B) {s : ℕ} (y : Fin s → B) (F : C ⥤ Complex A)
variable (hF : ∀ K : C, ∀ j, IsComplete B (y j) (DerivedCategory.Q.obj
  (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj (F.obj K))))

/-- 同じ指定分解に係数拡大と有限完備化を適用する元の関手。 -/
abbrev resolvedOrdinarySourceFunctor := F ⋙ complexResolutionFunctor A ⋙
  (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ finiteCompletionFunctor y

/-- 同じ元の複体への通常係数拡大。 -/
abbrev ordinaryTargetFunctor := F ⋙ (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)

/-- 同じ元の複体への通常係数拡大と有限完備化。 -/
abbrev completedOrdinaryTargetFunctor := ordinaryTargetFunctor f F ⋙ finiteCompletionFunctor y

/-- 同じ通常係数拡大からの元の標準有限完備化単位。 -/
def ordinaryTargetUnit : ordinaryTargetFunctor f F ⋙ DerivedCategory.Q ⟶
    completedOrdinaryTargetFunctor f y F ⋙ DerivedCategory.Q where
  app K := DerivedCategory.Q.map (finiteCompletionUnit y ((ordinaryTargetFunctor f F).obj K))
  naturality K L g := by
    have h := congrArg DerivedCategory.Q.map (finiteCompletionUnit_naturality y
      ((ordinaryTargetFunctor f F).map g))
    simpa only [resolvedOrdinarySourceFunctor, completedOrdinaryTargetFunctor,
      ordinaryTargetFunctor, Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.map_comp] using h

/-- 指定された完備性により、同じ元の標準単位は自然同型となる。 -/
def ordinaryTargetUnitIso : ordinaryTargetFunctor f F ⋙ DerivedCategory.Q ≅
    completedOrdinaryTargetFunctor f y F ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K => by
    haveI : IsIso ((ordinaryTargetUnit f y F).app K) :=
      finiteCompletionUnit_isIso_of_isComplete y _ (hF K)
    exact asIso ((ordinaryTargetUnit f y F).app K))
    (by intro K L g; exact (ordinaryTargetUnit f y F).naturality g)

/-- 元の指定分解の増大を、同じ通常係数拡大と完備化で写す自然変換。 -/
def resolvedOrdinaryAugmentation : resolvedOrdinarySourceFunctor f y F ⋙ DerivedCategory.Q ⟶
    completedOrdinaryTargetFunctor f y F ⋙ DerivedCategory.Q where
  app K := DerivedCategory.Q.map ((finiteCompletionFunctor y).map
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      ((complexResolutionAugmentation A).app (F.obj K))))
  naturality K L g := by
    have h := congrArg (fun t => DerivedCategory.Q.map ((finiteCompletionFunctor y).map
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map t)))
        ((complexResolutionAugmentation A).naturality (F.map g))
    simpa only [resolvedOrdinarySourceFunctor, completedOrdinaryTargetFunctor,
      ordinaryTargetFunctor, Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.map_comp] using h

/-- 同じ指定増大と同じ標準単位からなる、元の通常係数拡大への自然な比較。 -/
def resolvedOrdinaryComparison : resolvedOrdinarySourceFunctor f y F ⋙ DerivedCategory.Q ⟶
    ordinaryTargetFunctor f F ⋙ DerivedCategory.Q :=
  resolvedOrdinaryAugmentation f y F ≫ (ordinaryTargetUnitIso f y F hF).inv

/-- 元の増大が係数拡大で擬同型なら、同じ比較のその成分は同型。 -/
theorem resolvedOrdinaryComparison_app_isIso (K : C)
    (hq : QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      ((complexResolutionAugmentation A).app (F.obj K)))) :
    IsIso ((resolvedOrdinaryComparison f y F hF).app K) := by
  haveI := hq
  haveI := finiteCompletionFunctor_map_quasiIso y
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      ((complexResolutionAugmentation A).app (F.obj K)))
  haveI : IsIso ((resolvedOrdinaryAugmentation f y F).app K) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  change IsIso ((resolvedOrdinaryAugmentation f y F).app K ≫ (ordinaryTargetUnitIso f y F hF).inv.app K)
  infer_instance

/-- 同じ元の標準単位との合成は、元の指定分解の係数拡大した増大そのもの。 -/
@[reassoc] theorem unit_comp_resolvedOrdinaryComparison (K : C) :
    DerivedCategory.Q.map (finiteCompletionUnit y
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj
          ((complexResolutionFunctor A).obj (F.obj K)))) ≫
      (resolvedOrdinaryComparison f y F hF).app K =
    DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      ((complexResolutionAugmentation A).app (F.obj K))) := by
  let q := ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
    ((complexResolutionAugmentation A).app (F.obj K))
  have h := congrArg DerivedCategory.Q.map (finiteCompletionUnit_naturality y q)
  simp only [Functor.map_comp] at h
  change DerivedCategory.Q.map (finiteCompletionUnit y _) ≫
    (DerivedCategory.Q.map ((finiteCompletionFunctor y).map q) ≫ (ordinaryTargetUnitIso f y F hF).inv.app K) = _
  rw [← Category.assoc, ← h, Category.assoc]
  change DerivedCategory.Q.map q ≫ ((ordinaryTargetUnitIso f y F hF).hom.app K ≫
    (ordinaryTargetUnitIso f y F hF).inv.app K) = _
  rw [Iso.hom_inv_id_app]
  change DerivedCategory.Q.map q ≫ 𝟙 _ = DerivedCategory.Q.map q
  exact Category.comp_id _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
