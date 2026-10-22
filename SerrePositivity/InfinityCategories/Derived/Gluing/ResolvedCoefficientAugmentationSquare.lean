module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolvedCoefficientMappingSpan
public import SerrePositivity.InfinityCategories.Derived.Gluing.YonedaPostcomposition

/-! 同じ二つの augmentation の係数比較は、元の全鎖写像の厳密な可換四角形をなす。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

def dgGluingResolvedCoefficientEvaluation :
    (dgGluingResolvedModule R C N).val.obj (Opposite.op c) ⟶ N.obj (Opposite.op c) :=
  (moduleEvaluation R C c).map (dgGluingResolvedModuleAugmentation R C N)

lemma dgGluingResolvedCoefficientEvaluation_quasiIso :
    QuasiIso (dgGluingResolvedCoefficientEvaluation R C c N) :=
  dgGluingResolvedModuleAugmentation_quasiIso R C N c

lemma dgGluingResolvedCoefficientAugmentation_square :
    dgGluingResolvedCoefficientYonedaPre R C c (dgGluingResolvedModule R C N).val ≫
      dgGluingResolvedCoefficientHomPost R C c N =
    dgGluingResolvedCoefficientEvaluation R C c N ≫
      dgGluingResolvedCoefficientYonedaPre R C c N := by
  dsimp only [dgGluingResolvedCoefficientYonedaPre, dgGluingResolvedCoefficientHomPost,
    dgGluingResolvedCoefficientEvaluation]
  rw [Category.assoc, ← eHom_whisker_exchange, ← Category.assoc,
    dgGluingYonedaIso_inv_postcompose, Category.assoc]
  rfl

lemma dgGluingResolvedCoefficientAugmentation_space_square :
    complexPinchedMap.{u, max (u + 1) v}
        (dgGluingResolvedCoefficientYonedaPre R C c (dgGluingResolvedModule R C N).val) ≫
      complexPinchedMap (dgGluingResolvedCoefficientHomPost R C c N) =
    complexPinchedMap (dgGluingResolvedCoefficientEvaluation R C c N) ≫
      dgGluingDerivedCoefficientHomSpanRight R C c N := by
  rw [← complexPinchedMap_comp]
  change complexPinchedMap.{u, max (u + 1) v} _ =
    complexPinchedMap _ ≫ complexPinchedMap _
  rw [← complexPinchedMap_comp, dgGluingResolvedCoefficientAugmentation_square]

lemma dgGluingResolvedCoefficientEvaluation_space_equivalence :
    IsSimplicialHomotopyEquivalence
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingResolvedCoefficientEvaluation R C c N)) := by
  let : QuasiIso (dgGluingResolvedCoefficientEvaluation R C c N) :=
    dgGluingResolvedCoefficientEvaluation_quasiIso R C c N
  exact complexPinchedMap_quasiIso_equivalence _

end SerrePositivity.InfinityCategories
