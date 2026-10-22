module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionExt
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleNaturality

/-! 共通対角の引き戻しから矢印 Hom への比較は、元の二三角形を保ち全族で単射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

lemma dgGluingArrowCompositionPullbackToHom_hom_ext
    (u v : T ⟶ dgGluingArrowCompositionPullback f g)
    (h : u ≫ dgGluingArrowCompositionPullbackToHom f g =
      v ≫ dgGluingArrowCompositionPullbackToHom f g) : u = v := by
  have ht := congrArg (dgGluingArrowHomTrianglePairOfInterval
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)) h
  rw [dgGluingArrowHomTriangles_naturality, dgGluingArrowHomTriangles_naturality,
    dgGluingArrowCompositionPullbackToHom_triangles] at ht
  apply pullback.hom_ext
  · apply dgGluingFirstFixedComposition_hom_ext_triangle f d
    apply uncurry_injective
    exact congrArg DGGluingArrowHomTrianglePair.first ht
  · apply compositionCorrespondence_hom_ext_triangle a g
    apply uncurry_injective
    exact congrArg DGGluingArrowHomTrianglePair.second ht

instance dgGluingArrowCompositionPullbackToHom_mono :
    Mono (dgGluingArrowCompositionPullbackToHom f g) where
  right_cancellation u v h := dgGluingArrowCompositionPullbackToHom_hom_ext f g u v h

end SerrePositivity.InfinityCategories
