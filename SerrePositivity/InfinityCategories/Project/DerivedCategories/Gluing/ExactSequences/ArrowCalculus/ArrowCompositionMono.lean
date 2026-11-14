module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ArrowCalculus.ArrowCompositionPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstFixedCompositionExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.ArrowHomTriangleNaturality

/-! 共通対角の引き戻しから矢印 Hom への比較は、元の二三角形を保ち全族で単射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

lemma dgGluingArrowCompositionPullbackToHom_hom_ext
    (u v : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullback f g)
    (h : u ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g =
      v ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g) : u = v := by
  have ht := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTriangles_naturality, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTriangles_naturality,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom_triangles] at ht
  apply pullback.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedComposition_hom_ext_triangle f d
    apply uncurry_injective
    exact congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.first ht
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_hom_ext_triangle a g
    apply uncurry_injective
    exact congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.second ht

instance dgGluingArrowCompositionPullbackToHom_mono :
    Mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullbackToHom f g) where
  right_cancellation u v h := dgGluingArrowCompositionPullbackToHom_hom_ext f g u v h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
