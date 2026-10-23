module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientMapping
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientEvaluationSection
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration

/-! 元の係数から実導来端点間 Hom への選択された比較と、元の augmentation の厳密な回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingChosenCoefficientMappingComparison (c : C) (d : D) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (M.value c d)) ⟶
    InfinityCategories.pinchedHom
      (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex c)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex d))) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (dgGluingCoefficientEvaluationSection.{u, v, max u v w} R C c (M.rightAt d)) ≫
    dgGluingDerivedCoefficientMappingComparison R C D M c d

lemma dgGluingChosenCoefficientMappingComparison_equivalence (c : C) (d : D) :
    IsSimplicialHomotopyEquivalence (dgGluingChosenCoefficientMappingComparison R C D M c d) :=
  (dgGluingCoefficientEvaluationSection_equivalence.{u, v, max u v w}
    R C c (M.rightAt d)).ulift.comp
      (dgGluingDerivedCoefficientMappingComparison_equivalence R C D M c d)

lemma dgGluingChosenCoefficientMappingComparison_augmentation (c : C) (d : D) :
    dgGluingChosenCoefficientMappingComparison R C D M c d ≫
      (dgGluingDerivedCoefficientEndpointIso R C D M c d).inv ≫
      dgGluingUniverseDerivedCoefficientHomSpanLeft.{u, v, w} R C c (M.rightAt d) =
      dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c (M.rightAt d) := by
  rw [dgGluingChosenCoefficientMappingComparison, Category.assoc,
    dgGluingDerivedCoefficientMappingComparison_augmentation, ← Category.assoc,
    ← Functor.map_comp, dgGluingCoefficientEvaluationSection_augmentation,
    CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories
