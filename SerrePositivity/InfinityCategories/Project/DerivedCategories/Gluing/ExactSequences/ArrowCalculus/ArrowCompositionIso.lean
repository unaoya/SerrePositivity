module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.ArrowHomCompositionLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ArrowCalculus.ArrowCompositionMono

/-! 矢印 Hom と同じ二合成対応の対角引き戻しは、全単体を保持して厳密に同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

lemma dgGluingArrowHomToCompositionFamily_comp
    (h : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomToCompositionFamily f g h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g =
      h := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTriangles_naturality, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom_triangles]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.ext
  · change (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomToCompositionFamily f g h ≫ pullback.fst _ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f d = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomToCompositionFamily_first, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomFirstComposition,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionLift_evaluation]
  · change (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomToCompositionFamily f g h ≫ pullback.snd _ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation a g = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomToCompositionFamily_last, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomLastComposition,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_evaluation]

def dgGluingArrowHomToComposition :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge)) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullback f g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomToCompositionFamily f g (𝟙 _)

lemma dgGluingArrowHomToComposition_toHom :
    dgGluingArrowHomToComposition f g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g = 𝟙 _ :=
  dgGluingArrowHomToCompositionFamily_comp f g (𝟙 _)

lemma dgGluingArrowCompositionToHom_toComposition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g ≫ dgGluingArrowHomToComposition f g = 𝟙 _ := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g)).1
  rw [Category.assoc, dgGluingArrowHomToComposition_toHom, Category.comp_id, Category.id_comp]

def dgGluingArrowCompositionIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullback f g ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge)) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g
  inv := dgGluingArrowHomToComposition f g
  hom_inv_id := dgGluingArrowCompositionToHom_toComposition f g
  inv_hom_id := dgGluingArrowHomToComposition_toHom f g

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
