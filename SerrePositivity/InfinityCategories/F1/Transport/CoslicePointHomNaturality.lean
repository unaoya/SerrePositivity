module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom

/-! # 実 coslice 内の元の射の類は、同じ始点からの点の射の自然性を与える -/

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
variable {X : SSet.{u}} {x a b : X _⦋0⦌}
  (s : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a) _⦋0⦌)
  (t : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) b) _⦋0⦌)

/-- 元の coslice の射の底への像を、指定した元の fiber の端点で読む。 -/
def cosliceFiberHomProjection (m : HomotopyCategory.mk s.val ⟶ HomotopyCategory.mk t.val) :
    HomotopyCategory.mk a ⟶ HomotopyCategory.mk b :=
  (eqToIso (congrArg HomotopyCategory.mk (s.property.trans (pinchedConstant_zero a)))).inv ≫
    (hoFunctor.map (sliceUnderProjection (yonedaEquiv.symm x))).toFunctor.map m ≫
    (eqToIso (congrArg HomotopyCategory.mk (t.property.trans (pinchedConstant_zero b)))).hom

/-- 同じ coslice 内の実射の類は、元の点の射と底の射との合成式を保つ。 -/
theorem cosliceFiberPointHom_comp_projection [Quasicategory X]
    (m : HomotopyCategory.mk s.val ⟶ HomotopyCategory.mk t.val) :
    cosliceFiberPointHom s ≫ cosliceFiberHomProjection s t m = cosliceFiberPointHom t := by
  obtain ⟨l, rfl⟩ := homotopyCategory_homMk_surjective s.val t.val m
  let e := SSet.Edge.ofTruncated l
  have ht := homMk_transport (s.property.trans (pinchedConstant_zero a))
    (t.property.trans (pinchedConstant_zero b))
    (l.map ((truncation 2).map (sliceUnderProjection (yonedaEquiv.symm x))))
    (cosliceFiberBaseEdge s t e).toTruncated rfl
  have hp : cosliceFiberHomProjection s t (Truncated.HomotopyCategory.homMk l) =
      Truncated.HomotopyCategory.homMk (cosliceFiberBaseEdge s t e).toTruncated := ht
  rw [hp]
  exact Truncated.HomotopyCategory.homMk_comp_homMk
    (cosliceFiberEdgeCompStruct s t e).toTruncated

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberHomProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberHomProjection := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberHomProjection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberPointHom_comp_projection := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom_comp_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberHomProjection._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberHomProjection._proof_1
