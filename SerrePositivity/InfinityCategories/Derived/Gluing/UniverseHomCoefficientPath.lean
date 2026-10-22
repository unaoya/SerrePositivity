module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientPathEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePathPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.KanPathPullbackTransport

/-! 元の Hom と二作用を変えず、通常係数 path 比較を主比較と同じ共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded
open HomotopyLimits
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingUniverseHomCoefficientActions (X Y : DGGluingObject R C D M) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
        complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) ≫
    (uliftTensorIso _ _).hom

def dgGluingUniverseHomCoefficientPathComparison (X Y : DGGluingObject R C D M) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (dgGluingHomCoefficientPathPullbackComparison R C D M X Y) ≫
    (dgGluingUliftPathPullbackIso.{max u v w, max (u + 1) v w}
      (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
        complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y))).hom

lemma dgGluingUniverseHomCoefficientPathComparison_equivalence
    (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence
      (dgGluingUniverseHomCoefficientPathComparison R C D M X Y) := by
  apply (dgGluingHomotopyEquivalence_postcomp_iso_iff _ _).mpr
  exact (dgGluingHomCoefficientPathPullbackComparison_equivalence R C D M X Y).ulift

lemma dgGluingUniverseHomCoefficientPathComparison_path (X Y : DGGluingObject R C D M) :
    dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ pullback.fst _ _ =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (dgGluingHomCoefficientIntervalPath R C D M X Y) ≫
        (uliftIntervalHomIso _).hom := by
  rw [dgGluingUniverseHomCoefficientPathComparison, Category.assoc,
    dgGluingUliftPathPullbackIso_path, ← Category.assoc, ← Functor.map_comp,
    dgGluingHomCoefficientPathPullbackComparison_path]

lemma dgGluingUniverseHomCoefficientPathComparison_inputs (X Y : DGGluingObject R C D M) :
    dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  rw [dgGluingUniverseHomCoefficientPathComparison, Category.assoc,
    dgGluingUliftPathPullbackIso_inputs, ← Functor.map_comp,
    dgGluingHomCoefficientPathPullbackComparison_inputs]

end SerrePositivity.InfinityCategories
