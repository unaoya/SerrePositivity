module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedModuleArrow
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxFixedInputVertices
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedCompatibility
public import SerrePositivity.InfinityCategories.Core.CatInfinity.HomotopySimplexFaces

/-! 元の lax 比較の各頂点は、同じ二入力と元の augmentation の導来像を持つ三つ組。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial

lemma dgGluingCurryHomotopy_vertex_edge {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (x : A _⦋0⦌) :
    intervalFunctorVertexEdge
      ((curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)).app (Opposite.op ⦋0⦌) x) =
      (simplicialHomotopyVertexEdge H x).edge := by
  rw [intervalFunctorVertexEdge_curry, pinchedConstant_one]
  change H.h.app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
  rw [← F2.homotopyIntervalEdge_simplex]
  rfl

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseLaxComparison_vertex_image (X : DGGluingObject R C D M) :
    (dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X)) =
      dgGluingLaxFixedInputVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)
        (ULift.up (Simplex.vertex X.left)) (ULift.up (Simplex.vertex X.right))
        (dgGluingDerivedModuleArrow R C D M X.left X.right (dgGluingAugmentation R C D M X)) := by
  let x : ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M))) _⦋0⦌ := ULift.up (Simplex.vertex X)
  apply (F2.laxPullbackVertexEquiv _ _).injective
  change F2.laxPullbackVertexData _ _ _ =
    F2.laxPullbackVertexData _ _ (F2.laxPullbackVertexOfData _ _ _)
  rw [F2.laxPullbackVertexData_ofData]
  apply F2.LaxPullbackVertexData.ext
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingUniverseDerivedNerveLaxComparison_fst R C D M) (Opposite.op ⦋0⦌))
        x
    change _ = ULift.up (Simplex.vertex X.left)
    exact h.trans (dgGluingUniverseNerveMap_vertex.{u, max u v w, v, max (u + 1) v w}
      (dgGluingLeft R C D M) X)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingUniverseDerivedNerveLaxComparison_snd R C D M) (Opposite.op ⦋0⦌))
        x
    change _ = ULift.up (Simplex.vertex X.right)
    exact h.trans (dgGluingUniverseNerveMap_vertex.{u, max u v w, w, max (u + 1) v w}
      (dgGluingRight R C D M) X)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingUniverseDerivedNerveLaxComparison_arrow R C D M) (Opposite.op ⦋0⦌))
        x
    change (F2.laxPullbackArrow _ _).app (Opposite.op ⦋0⦌)
      ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X))) =
      (dgGluingUniverseDerivedAugmentationArrowFamily R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X)) at h
    change intervalFunctorVertexEdge _ = _
    rw [h, dgGluingUniverseDerivedAugmentationArrowFamily, dgGluingCurryHomotopy_vertex_edge,
      dgGluingUniverseDerivedAugmentationHomotopy_vertex_edge]
    rfl

end SerrePositivity.InfinityCategories
