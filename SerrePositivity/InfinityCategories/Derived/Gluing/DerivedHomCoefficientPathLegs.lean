module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedHomCoefficientPath

/-! 導来係数 path 比較は、元の全区間族の導来像と元の左右 Hom 射影を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded HomotopyLimits
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedHomCoefficientIntervalPath (X Y : DGGluingObject R C D M) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (dgGluingHomCoefficientIntervalPath R C D M X Y) ≫
    (uliftIntervalHomIso _).hom ≫
      (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
        (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)

lemma dgGluingDerivedHomCoefficientPathComparison_path (X Y : DGGluingObject R C D M) :
    dgGluingDerivedHomCoefficientPathComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingDerivedHomCoefficientIntervalPath R C D M X Y := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ k)
    (dgGluingKanPathPullbackTransport_path
      (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
      (dgGluingUniverseHomCoefficientActions R C D M X Y))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  have h := congrArg (fun k => k ≫ (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
    (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right))
      (dgGluingUniverseHomCoefficientPathComparison_path R C D M X Y)
  simpa only [dgGluingDerivedHomCoefficientIntervalPath,
    dgGluingUniverseHomCoefficientActions, Category.assoc] using h

lemma dgGluingDerivedHomCoefficientPathComparison_inputs (X Y : DGGluingObject R C D M) :
    dgGluingDerivedHomCoefficientPathComparison R C D M X Y ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun k => dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫ k)
    (dgGluingKanPathPullbackTransport_inputs
      (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
      (dgGluingUniverseHomCoefficientActions R C D M X Y))).trans
        (dgGluingUniverseHomCoefficientPathComparison_inputs R C D M X Y)

lemma dgGluingDerivedHomCoefficientIntervalPath_uncurry
    (X Y : DGGluingObject R C D M) :
    uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) =
      uncurry ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (dgGluingHomCoefficientIntervalPath R C D M X Y) ≫
        (uliftIntervalHomIso _).hom) ≫
          dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right := by
  rw [dgGluingDerivedHomCoefficientIntervalPath, ← Category.assoc, uncurry_natural_right]

end SerrePositivity.InfinityCategories
