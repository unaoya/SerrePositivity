module
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionFiberPoint
public import SerrePositivity.KST.Fibration.CosliceTransportPointHom
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso

/-! # 同じ復元の実 fiber 点の等式輸送と頂点同型は、指定分類射に反映される -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- 底頂点を等式で揃えた同じ実点の分類射は、元の値の等式同型による後合成。 -/
theorem scaffoldReconstructionFiberPoint_eqToHom_transport {b b' : B _⦋0⦌}
    (h : b = b') (w : (vertexFiber p b) _⦋0⦌) :
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b w) ≫
      (eqToIso (congrArg (fun z => HomotopyCategory.mk
        ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up z))) h)).hom =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b'
      ((eqToHom (congrArg (vertexFiber p) h)).app (Opposite.op ⦋0⦌) w)) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, eqToHom_refl]
  rfl

/-- 同じ実 fiber 内の頂点同型は、同じ復元像の点の分類射の等式を与える。 -/
theorem scaffoldReconstructionFiberPoint_pointHom_eq_of_vertexIso (b : B _⦋0⦌)
    {v w : (vertexFiber p b) _⦋0⦌} (e : VertexIso v w) :
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b v) =
      cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b w) := by
  let F := leftStraighteningInfinityDiagram p
  let M := vertexFiberMap p (smallLeftUnstraighteningProjection F)
    (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p) b
  let h := uliftVertexIso.{u, u + 1} (VertexIso.map e M)
  exact cosliceFiberPointHom_eq_of_vertexIso (VertexIso.map h
    ((smallLeftUnstraighteningFiberIso F b).hom ≫
      (leftUnstraighteningFiberIso F (ULift.up b)).hom))

end SerrePositivity.KST.Fibration
