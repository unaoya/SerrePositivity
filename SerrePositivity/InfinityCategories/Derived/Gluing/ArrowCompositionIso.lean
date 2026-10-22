module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionMono

/-! 矢印 Hom と同じ二合成対応の対角引き戻しは、全単体を保持して厳密に同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

lemma dgGluingArrowHomToCompositionFamily_comp
    (h : T ⟶ intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge))) :
    dgGluingArrowHomToCompositionFamily f g h ≫ dgGluingArrowCompositionPullbackToHom f g =
      h := by
  apply dgGluingArrowHomTrianglePairOfInterval_injective
  rw [dgGluingArrowHomTriangles_naturality, dgGluingArrowCompositionPullbackToHom_triangles]
  apply DGGluingArrowHomTrianglePair.ext
  · change (Δ[2] ◁ (dgGluingArrowHomToCompositionFamily f g h ≫ pullback.fst _ _)) ≫
      dgGluingFirstFixedCompositionEvaluation f d = _
    rw [dgGluingArrowHomToCompositionFamily_first, dgGluingArrowHomFirstComposition,
      dgGluingFirstFixedCompositionLift_evaluation]
  · change (Δ[2] ◁ (dgGluingArrowHomToCompositionFamily f g h ≫ pullback.snd _ _)) ≫
      compositionCorrespondenceEvaluation a g = _
    rw [dgGluingArrowHomToCompositionFamily_last, dgGluingArrowHomLastComposition,
      dgGluingLastFixedCompositionLift_evaluation]

def dgGluingArrowHomToComposition :
    intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge)) ⟶ dgGluingArrowCompositionPullback f g :=
  dgGluingArrowHomToCompositionFamily f g (𝟙 _)

lemma dgGluingArrowHomToComposition_toHom :
    dgGluingArrowHomToComposition f g ≫ dgGluingArrowCompositionPullbackToHom f g = 𝟙 _ :=
  dgGluingArrowHomToCompositionFamily_comp f g (𝟙 _)

lemma dgGluingArrowCompositionToHom_toComposition :
    dgGluingArrowCompositionPullbackToHom f g ≫ dgGluingArrowHomToComposition f g = 𝟙 _ := by
  apply (cancel_mono (dgGluingArrowCompositionPullbackToHom f g)).1
  rw [Category.assoc, dgGluingArrowHomToComposition_toHom, Category.comp_id, Category.id_comp]

def dgGluingArrowCompositionIso :
    dgGluingArrowCompositionPullback f g ≅
      intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
        (functorVertex (SSet.yonedaEquiv.symm g.edge)) where
  hom := dgGluingArrowCompositionPullbackToHom f g
  inv := dgGluingArrowHomToComposition f g
  hom_inv_id := dgGluingArrowCompositionToHom_toComposition f g
  inv_hom_id := dgGluingArrowHomToComposition_toHom f g

end SerrePositivity.InfinityCategories
