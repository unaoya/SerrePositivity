module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy

/-! # The original whole mixed triangles and all their actual boundary families across centers -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangles
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (p : Index C)

abbrev oldBoundary := CoherentLiftMixedComparison.boundary p.source.inner p.middle.inner
  p.target p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre)
abbrev oldTriangle (side : Bool) := CoherentLiftMixedComparison.triangle hcof hfib
  p.source.inner p.middle.inner p.target p.final p.pre.map p.center p.post
  (FramedResolution.frameMap p.pre) side
abbrev oldFace (side : Bool) (k : Fin 3) :=
  (CoherentLiftMixedComparison.data hcof hfib p.source.inner p.middle.inner p.target p.final
    p.pre.map p.center p.post (FramedResolution.frameMap p.pre) side).faces k
abbrev oldDiagonal := CoherentLiftMixedComparison.diagonal hcof hfib p.source.inner p.middle.inner
  p.target p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre)
abbrev oldInclusion := CoherentLiftRelative.vertexInclusion p.middle.inner p.target p.center

include hcof in
lemma vertexBoundary_lifted : (vertexBoundary C).app p = UniverseLift.map.{u} (oldBoundary C p)
  := by
  have hp := CoherentLiftRelative.postLeft_vertices hcof p.middle.inner p.target p.final
    p.center p.post
  change oldInclusion C p ≫ (CoherentLiftTuples.interpolation hcof p.middle.inner p.target
    p.center ≫ _) = _ at hp
  rw [← Category.assoc, CoherentLiftTuples.interpolation_vertices] at hp
  change UniverseLift.map.{u} ((ResolutionArrowTuples.vertexData C).app (a C p)) ≫
    UniverseLift.map.{u} ((ResolutionArrowDiagram.fibers C).map (ab C p ≫ bd C p)) = _
  rw [← UniverseLift.map_comp, commutes, CategoryTheory.Functor.map_comp]
  apply congrArg (fun k => UniverseLift.map.{u} k)
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (ResolutionArrowDiagram.fibers C).map (cd C p))
      ((congrArg (fun k => (ResolutionArrowTuples.vertexData C).app (a C p) ≫ k)
        (ResolutionArrowElementary.post_fibers p.middle p.target p.final p.center p.post)).trans
          hp))).trans
    (congrArg (fun k => CoherentLiftRelative.postBoundary p.middle.inner p.target p.final
      p.center p.post ≫ k) (ResolutionArrowElementary.pre_fibers
        p.source p.middle p.final p.pre (p.center ≫ p.post.base)))

abbrev triangle (side : Bool) : (parameters C).obj p ⊗
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2) ⟶
      UniverseLift.obj.{u} ((smallValues C).obj p) :=
  UniverseLift.simplexTensorMap.{u}
    (RelativeChoiceSpace.family (oldInclusion C p) (oldBoundary C p) (oldTriangle C hcof hfib p
      side))

abbrev face (side : Bool) (k : Fin 3) : (parameters C).obj p ⊗
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶
      UniverseLift.obj.{u} ((smallValues C).obj p) :=
  UniverseLift.simplexTensorMap.{u}
    (RelativeChoiceSpace.family (oldInclusion C p) (oldBoundary C p) (oldFace C hcof hfib p side k))

abbrev diagonal : (parameters C).obj p ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶
    UniverseLift.obj.{u} ((smallValues C).obj p) :=
  UniverseLift.simplexTensorMap.{u}
    (RelativeChoiceSpace.family (oldInclusion C p) (oldBoundary C p) (oldDiagonal C hcof hfib p))

lemma triangle_face (side : Bool) (k : Fin 3) :
    (parameters C).obj p ◁ SSet.stdSimplex.δ k ≫ triangle C hcof hfib p side =
      face C hcof hfib p side k := by
  apply (UniverseLift.simplexTensorMap_operator.{u} (SimplexCategory.δ k) _).trans
  apply congrArg (fun k => UniverseLift.simplexTensorMap.{u} k)
  exact (RelativeChoiceSpace.family_naturality (oldInclusion C p) (oldBoundary C p)
    (oldTriangle C hcof hfib p side) (SSet.stdSimplex.δ k)).symm.trans
      (congrArg (RelativeChoiceSpace.family (oldInclusion C p) (oldBoundary C p))
        (CoherentLiftMixedComparison.triangle_face hcof hfib p.source.inner p.middle.inner
          p.target p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre) side k))

lemma triangle_diagonal (side : Bool) :
    (parameters C).obj p ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle C hcof hfib p side =
      diagonal C hcof hfib p := by
  apply (UniverseLift.simplexTensorMap_operator.{u} (SimplexCategory.δ (1 : Fin 3)) _).trans
  apply congrArg (fun k => UniverseLift.simplexTensorMap.{u} k)
  exact (RelativeChoiceSpace.family_naturality (oldInclusion C p) (oldBoundary C p)
    (oldTriangle C hcof hfib p side) (SSet.stdSimplex.δ (1 : Fin 3))).symm.trans
      (congrArg (RelativeChoiceSpace.family (oldInclusion C p) (oldBoundary C p))
        (CoherentLiftMixedComparison.triangle_diagonal hcof hfib p.source.inner p.middle.inner
          p.target p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre) side))

lemma shared_diagonal : (parameters C).obj p ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    triangle C hcof hfib p true = (parameters C).obj p ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
      triangle C hcof hfib p false :=
  (triangle_diagonal C hcof hfib p true).trans (triangle_diagonal C hcof hfib p false).symm

lemma triangle_vertices (side : Bool) :
    (vertexInclusion C).app p ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
      triangle C hcof hfib p side =
    fst ((vertexParameters C).obj p) (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫
      (vertexBoundary C).app p := by
  apply (UniverseLift.simplexTensorMap_source.{u} (oldInclusion C p) _).trans
  apply Eq.trans ?_ (congrArg (fun k => fst _ _ ≫ k) (vertexBoundary_lifted C hcof p).symm)
  have ht := CoherentLiftMixedComparison.triangle_fixed_boundary hcof hfib
    p.source.inner p.middle.inner p.target p.final p.pre.map p.center p.post
    (FramedResolution.frameMap p.pre) side
  have hp := (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ oldBoundary C p)
      (UniverseLift.whole_projection (CoherentLiftRelative.vertices p.middle.inner p.target
        p.center) (SSet.stdSimplex.obj (SimplexCategory.mk 2))))
  exact (congrArg (fun k => UniverseLift.simplexTensorMap.{u} k) (ht.trans hp)).trans
    (UniverseLift.simplexTensorMap_constant (oldBoundary C p) 2)

lemma triangle_recover (side : Bool) : UniverseLift.lowerSimplexTensor
    (triangle C hcof hfib p side) = RelativeChoiceSpace.family (oldInclusion C p)
      (oldBoundary C p) (oldTriangle C hcof hfib p side) :=
  UniverseLift.lowerSimplexTensor_simplexTensorMap _

lemma face_recover (side : Bool) (k : Fin 3) : UniverseLift.lowerSimplexTensor
    (face C hcof hfib p side k) = RelativeChoiceSpace.family (oldInclusion C p)
      (oldBoundary C p) (oldFace C hcof hfib p side k) :=
  UniverseLift.lowerSimplexTensor_simplexTensorMap _

lemma diagonal_recover : UniverseLift.lowerSimplexTensor
    (diagonal C hcof hfib p) = RelativeChoiceSpace.family (oldInclusion C p)
      (oldBoundary C p) (oldDiagonal C hcof hfib p) :=
  UniverseLift.lowerSimplexTensor_simplexTensorMap _

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangles
