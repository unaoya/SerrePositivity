module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceFiberVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber

/-! # 指定した空間値の点の射を、同じ小さい unstraightening の実 fiber 点にする -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 指定した一点空間からの射の一本の実辺を、同じ pointed-space fiber の点にする。 -/
def pointedSpaceFiberPointOfHom {s : SpaceInfinity.{u} _⦋0⦌}
    (a : HomotopyCategory.mk pointSpaceVertex ⟶ HomotopyCategory.mk s) :
    (vertexFiber pointedSpaceProjection s) _⦋0⦌ :=
  edgeToCosliceFiberVertex (SSet.Edge.ofTruncated
    (Classical.choose (homotopyCategory_homMk_surjective _ _ a)))

/-- 選んだ点の元の辺の類は、指定された同じ一点空間からの射そのもの。 -/
theorem pointedSpaceFiberPointOfHom_hom {s : SpaceInfinity.{u} _⦋0⦌}
    (a : HomotopyCategory.mk pointSpaceVertex ⟶ HomotopyCategory.mk s) :
    Truncated.HomotopyCategory.homMk
      (cosliceFiberVertexToEdge (pointedSpaceFiberPointOfHom a)).toTruncated = a := by
  have he := (cosliceFiberVertexEquiv pointSpaceVertex s).apply_symm_apply
    (SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective _ _ a)))
  have hh := congrArg (fun e => Truncated.HomotopyCategory.homMk e.toTruncated) he
  exact hh.trans (Classical.choose_spec (homotopyCategory_homMk_surjective _ _ a))

/-- 同じ pointed-space fiber の点を、同型だけで元の小さい unstraightening の実 fiber へ戻す。 -/
def smallUnstraighteningFiberPoint {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (s : (vertexFiber pointedSpaceProjection
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))) _⦋0⦌) :
    (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌ :=
  ((smallLeftUnstraighteningFiberIso F b).inv.app (Opposite.op ⦋0⦌)
    ((leftUnstraighteningFiberIso F (ULift.up b)).inv.app (Opposite.op ⦋0⦌) s)).down

/-- 宇宙を戻した同じ点を持ち上げ直すと、指定された元の pointed-space fiber 点を厳密に回収。 -/
theorem smallUnstraighteningFiberPoint_recover {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (s : (vertexFiber pointedSpaceProjection
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))) _⦋0⦌) :
    (leftUnstraighteningFiberIso F (ULift.up b)).hom.app (Opposite.op ⦋0⦌)
      ((smallLeftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (smallUnstraighteningFiberPoint F b s))) = s := by
  have hsmall := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    ((leftUnstraighteningFiberIso F (ULift.up b)).inv.app (Opposite.op ⦋0⦌) s))
    (smallLeftUnstraighteningFiberIso F b).inv_hom_id
  have hlarge := congrArg (fun m => m.app (Opposite.op ⦋0⦌) s)
    (leftUnstraighteningFiberIso F (ULift.up b)).inv_hom_id
  exact (congrArg ((leftUnstraighteningFiberIso F (ULift.up b)).hom.app
    (Opposite.op ⦋0⦌)) hsmall).trans hlarge

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceFiberPointOfHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedSpaceFiberPointOfHom := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceFiberPointOfHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedSpaceFiberPointOfHom_hom := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceFiberPointOfHom_hom

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.smallUnstraighteningFiberPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFiberPoint := _root_.SerrePositivity.InfinityCategories.F1.Transport.smallUnstraighteningFiberPoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFiberPoint_recover := _root_.SerrePositivity.InfinityCategories.F1.Transport.smallUnstraighteningFiberPoint_recover
