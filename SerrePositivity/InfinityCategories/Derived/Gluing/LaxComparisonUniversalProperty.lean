module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputTransport
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackFunctorCore
public import SerrePositivity.InfinityCategories.F1.Categories.CoreEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
/-!
概要：元 dg gluing は全試験関手について導来 lax pullback の ∞ 圏的普遍性を持つ。
方針：正本比較同値を全内部 Hom と core へ移し、F2 の同じ Kan 引き戻し同型を合成する。
規約：試験単体集合の quasicategory 性を仮定せず、元二入力と augmentation 全族を回収する。
使われ方：安定 gluing の普遍性と後続の完全射影・商の比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (K : SSet.{max (u + 1) v w})

def dgGluingLaxFunctorEquivalence :=
  (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).postcompose K

def dgGluingLaxFunctorCoreComparison :=
  quasicategoryCoreMap ((ihom K).map (dgGluingUniverseDerivedNerveLaxComparison R C D M)) ≫
    (F2.laxPullbackFunctorCoreIso K (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).hom

lemma dgGluingLaxFunctorCoreComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingLaxFunctorCoreComparison R C D M K) := by
  have he := ((dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence R C D M).postcompose K).core
  exact (dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (F2.laxPullbackFunctorCoreIso K (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M))).mpr he.isSimplicialHomotopyEquivalence

lemma dgGluingLaxFunctorCoreComparison_arrow :
    dgGluingLaxFunctorCoreComparison R C D M K ≫ pullback.fst _ _ =
      quasicategoryCoreMap ((ihom K).map (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)) := by
  rw [dgGluingLaxFunctorCoreComparison, Category.assoc, F2.laxPullbackFunctorCoreIso_arrow]
  change quasicategoryCoreFunctor.map ((ihom K).map
      (dgGluingUniverseDerivedNerveLaxComparison R C D M)) ≫
    quasicategoryCoreFunctor.map ((ihom K).map
      (F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))) = _
  rw [← Functor.map_comp, ← Functor.map_comp,
    dgGluingUniverseDerivedNerveLaxComparison_arrow]
  rfl
lemma dgGluingLaxFunctorCoreComparison_inputs :
    dgGluingLaxFunctorCoreComparison R C D M K ≫ pullback.snd _ _ =
      quasicategoryCoreMap ((ihom K).map
        (lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M))) := by
  rw [dgGluingLaxFunctorCoreComparison, Category.assoc, F2.laxPullbackFunctorCoreIso_inputs]
  change quasicategoryCoreFunctor.map ((ihom K).map
      (dgGluingUniverseDerivedNerveLaxComparison R C D M)) ≫
    quasicategoryCoreFunctor.map ((ihom K).map
      (pullback.snd _ _)) = _
  rw [← Functor.map_comp, ← Functor.map_comp,
    dgGluingUniverseDerivedNerveLaxComparison_inputs]
  rfl
end SerrePositivity.InfinityCategories
