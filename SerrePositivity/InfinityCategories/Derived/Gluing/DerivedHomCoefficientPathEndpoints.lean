module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedHomCoefficientPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePathPostEvaluation

/-! 導来 Hom 内の同じ区間族の両端は、元の νf と gμ の canonical な導来像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded HomotopyLimits
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingDerivedHomCoefficientIntervalPath_start (X Y : DGGluingObject R C D M) :
    dgGluingDerivedHomCoefficientIntervalPath R C D M X Y ≫
        evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w}
            (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right := by
  have h := dgGluingUliftIntervalPost_evaluate
    (dgGluingHomCoefficientIntervalPath R C D M X Y)
    (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right) 0
  have he := congrArg (fun k =>
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map k ≫
      dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
    (dgGluingHomCoefficientIntervalPath_start R C D M X Y)
  exact h.trans he

lemma dgGluingDerivedHomCoefficientIntervalPath_end (X Y : DGGluingObject R C D M) :
    dgGluingDerivedHomCoefficientIntervalPath R C D M X Y ≫
        evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w}
            (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right := by
  have h := dgGluingUliftIntervalPost_evaluate
    (dgGluingHomCoefficientIntervalPath R C D M X Y)
    (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right) 1
  have he := congrArg (fun k =>
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map k ≫
      dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
    (dgGluingHomCoefficientIntervalPath_end R C D M X Y)
  exact h.trans he

end SerrePositivity.InfinityCategories
