module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomCoefficientPathEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniversePathPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KanPathPullbackTransport

/-! 元の Hom と二作用を変えず、通常係数 path 比較を主比較と同じ共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingUniverseHomCoefficientActions (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).hom

def dgGluingUniverseHomCoefficientPathComparison (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison R C D M X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPathPullbackIso.{max u v w, max (u + 1) v w}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y))).hom

lemma dgGluingUniverseHomCoefficientPathComparison_equivalence
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingUniverseHomCoefficientPathComparison R C D M X Y) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_postcomp_iso_iff _ _).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison_equivalence R C D M X Y).ulift

lemma dgGluingUniverseHomCoefficientPathComparison_path (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ pullback.fst _ _ =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso _).hom := by
  rw [dgGluingUniverseHomCoefficientPathComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPathPullbackIso_path, ← Category.assoc, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison_path]

lemma dgGluingUniverseHomCoefficientPathComparison_inputs (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y))) := by
  rw [dgGluingUniverseHomCoefficientPathComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPathPullbackIso_inputs, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison_inputs]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
