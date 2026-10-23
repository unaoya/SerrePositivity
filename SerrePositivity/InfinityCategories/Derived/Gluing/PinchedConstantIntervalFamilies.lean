module
public import SerrePositivity.InfinityCategories.F1.Diagrams.CompositionTriangleFaces
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices

/-! 閉辺の定値 pinched 族は、元の辺そのものの全区間図式である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

lemma dgGluingPinchedConstantIntervalFamily {K X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (pinchedHom x y) _⦋0⦌) :
    intervalMappingUncurry ((SSet.const s : K ⟶ _) ≫ pinchedHomToIntervalMappingSpace x y) =
      fst (Δ[1] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm s.val := by
  rw [SSet.const_comp, pinchedHomToIntervalMappingSpace_vertex,
    intervalMappingUncurry_const_vertex]
  change fst _ K ≫ SSet.yonedaEquiv.symm
    (((intervalMappingEdgeVertexEquiv x y).symm
      ((intervalMappingEdgeVertexEquiv x y) (pinchedHomVertexEquiv x y s))).edge) = _
  rw [(intervalMappingEdgeVertexEquiv x y).symm_apply_apply (pinchedHomVertexEquiv x y s)]
  rfl

lemma dgGluingPinchedConstantIntervalFamily_post {K X Y : SSet.{u}}
    (F : X ⟶ Y) {x y : X _⦋0⦌} (s : (pinchedHom x y) _⦋0⦌) :
    intervalMappingUncurry (((SSet.const s : K ⟶ _) ≫ pinchedHomMap F x y) ≫
      pinchedHomToIntervalMappingSpace _ _) =
        fst (Δ[1] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋1⦌) s.val) := by
  rw [SSet.const_comp, dgGluingPinchedConstantIntervalFamily]
  rfl

end SerrePositivity.InfinityCategories
