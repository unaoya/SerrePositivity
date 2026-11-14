module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugActualComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges

/-! 対象宇宙を固定せず、実 augmentation prism の単位入力辺を元の閉辺へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)

lemma dgGluingSimplex_unit_map (X : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => X) (unitElement R X)).map F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => F.obj X) (unitElement R (F.obj X)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  change (F.map X X).f 0 (_root_.SerrePositivity.DifferentialGraded.unitElement R X).val = (_root_.SerrePositivity.DifferentialGraded.unitElement R (F.obj X)).val
  exact _root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement R F X

lemma dgGluingCommaPrism_unitEdge (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => X) (unitElement R X)) OrderHom.id =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_unitEdge R C E F X)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
