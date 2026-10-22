module
public import SerrePositivity.KST.Fibration.VertexFiberZeroSection
public import SerrePositivity.KST.Fibration.ScaffoldBaseChangeCoefficientNaturality

/-! # 復元射の実 fiber 点像と、底頂点の等式による指定点の輸送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- 元の実 fiber 点の、同じ scaffold 復元射による pointed-space fiber 像。 -/
def scaffoldReconstructionFiberPoint (b : B _⦋0⦌) (w : (vertexFiber p b) _⦋0⦌) :=
  smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram p) b
    ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
      (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p) b).app
        (Opposite.op ⦋0⦌) w)

/-- 底頂点の等式を含めて同じ fiber 点を指定すると、復元の分類射も同じ等式で輸送される。 -/
theorem scaffoldReconstructionFiberPoint_eq_transport {b b' : B _⦋0⦌} (h : b = b')
    (w : (vertexFiber p b) _⦋0⦌) (w' : (vertexFiber p b') _⦋0⦌)
    (hw : Eq.mp (congrArg (fun z => (vertexFiber p z) _⦋0⦌) h) w = w') :
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b w) ≫
      (eqToIso (congrArg (fun z => HomotopyCategory.mk
        ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up z))) h)).hom =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b' w') := by
  cases h
  change w = w' at hw
  subst w'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

end SerrePositivity.KST.Fibration
