module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.Core.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.Stable.IsomorphismFiberZero

/-!
概要：普遍 cofiber 図式を同じ右辺の fiber 図式として読む。
方針：元の零角と安定性の fiber/cofiber 判定を保持する。
規約：元の四角形を変更しない。使われ方：逆回転の零始点の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
namespace SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
open SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
variable (X : SSet.{u}) [Quasicategory X] [IsStable X] (z : (space X) _⦋0⦌)

/-- 元の cofiber 四角形は同じ右辺の fiber 四角形でもある。 -/
def fiberSquareAt : FiberSquare (squareRightArrow (squareDiagram z.val)) where
  square := squareDiagram z.val
  zero_corner := (fullSubcomplexOnVertices_vertex z).1
  right_edge :=
    (SSet.yonedaEquiv.symm_apply_apply (squareRightEdge ≫ squareDiagram z.val)).symm.trans
      (congrArg SSet.yonedaEquiv.symm (squareRightArrow_edge (squareDiagram z.val)).symm)
  isPullback := IsStable.pullback_of_pushout
    ⟨squareDiagram z.val, (fullSubcomplexOnVertices_vertex z).1⟩
    (fullSubcomplexOnVertices_vertex z).2

/-- 元の右辺が可逆なら同じ底辺の始点は零である。 -/
lemma zero_source_of_right_invertible
    (h : IsInvertibleEdge (squareRightArrow (squareDiagram z.val))) :
    IsZeroVertex (squareVertex (squareDiagram z.val) 0 0) :=
  (fiberSquareAt X z).zero_of_homMk_isIso h

end SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.fiberSquareAt (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.fiberSquareAt := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.fiberSquareAt

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.zero_source_of_right_invertible := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.zero_source_of_right_invertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.fiberSquareAt._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.fiberSquareAt._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.fiberSquareAt._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.fiberSquareAt._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.fiberSquareAt._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.fiberSquareAt._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.fiberSquareAt._proof_4 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.fiberSquareAt._proof_4
