module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedHomCoefficientPath

/-! 導来係数 path 比較は、元の全区間族の導来像と元の左右 Hom 射影を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedHomCoefficientIntervalPath (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso _).hom ≫
      (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)

lemma dgGluingDerivedHomCoefficientPathComparison_path (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientPathComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingDerivedHomCoefficientIntervalPath R C D M X Y := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_path
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientActions R C D M X Y))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  have h := congrArg (fun k => k ≫ (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientPathComparison_path R C D M X Y)
  simpa only [dgGluingDerivedHomCoefficientIntervalPath,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientActions, Category.assoc] using h

lemma dgGluingDerivedHomCoefficientPathComparison_inputs (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientPathComparison R C D M X Y ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y))) := by
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_inputs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientActions R C D M X Y))).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomCoefficientPathComparison_inputs R C D M X Y)

lemma dgGluingDerivedHomCoefficientIntervalPath_uncurry
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) =
      uncurry ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso _).hom) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right := by
  rw [dgGluingDerivedHomCoefficientIntervalPath, ← Category.assoc, uncurry_natural_right]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
