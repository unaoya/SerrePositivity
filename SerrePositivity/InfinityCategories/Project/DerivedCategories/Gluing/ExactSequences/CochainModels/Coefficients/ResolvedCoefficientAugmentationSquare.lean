module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ResolvedCoefficientMappingSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.YonedaPostcomposition

/-! 同じ二つの augmentation の係数比較は、元の全鎖写像の厳密な可換四角形をなす。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

def dgGluingResolvedCoefficientEvaluation :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val.obj (Opposite.op c) ⟶ N.obj (Opposite.op c) :=
  (moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation R C N)

lemma dgGluingResolvedCoefficientEvaluation_quasiIso :
    QuasiIso (dgGluingResolvedCoefficientEvaluation R C c N) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation_quasiIso R C N c

lemma dgGluingResolvedCoefficientAugmentation_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre R C c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N =
    dgGluingResolvedCoefficientEvaluation R C c N ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre R C c N := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost,
    dgGluingResolvedCoefficientEvaluation]
  rw [Category.assoc, ← eHom_whisker_exchange, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaIso_inv_postcompose, Category.assoc]
  rfl

lemma dgGluingResolvedCoefficientAugmentation_space_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre R C c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (dgGluingResolvedCoefficientEvaluation R C c N) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientHomSpanRight R C c N := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} _ =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, dgGluingResolvedCoefficientAugmentation_square]

lemma dgGluingResolvedCoefficientEvaluation_space_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (dgGluingResolvedCoefficientEvaluation R C c N)) := by
  let : QuasiIso (dgGluingResolvedCoefficientEvaluation R C c N) :=
    dgGluingResolvedCoefficientEvaluation_quasiIso R C c N
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
