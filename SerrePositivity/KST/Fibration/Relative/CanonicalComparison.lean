module
public import SerrePositivity.KST.Fibration.Relative.FirstRowSimplexComparison
public import SerrePositivity.KST.Fibration.VerdierCanonicalKernelSquareIso

/-!
概要：完成した c4 の全四角形同型を、同じ元の相対実現の二比較へ代入する。
方針：S-1 (a) から得た実同型を標準単体比較の消費側へ渡す。
規約：c5 の標準単体商比較だけを明示入力に残す。
使われ方：K-6 b・d と K-B3 が同じ SingleRelativeComparison を消費する入口。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の商の標準単体比較だけから、指定全四角形の相対実現界面を構成する。
方針：無条件の canonical 全四角形同型を既存の二比較の構成へ代入する。
規約：c5 の供給自体の存在は主張せず、c4 の存在仮定は取らない。
使われ方：Sp の実供給を元の fiber 比較の非負次数 π 同型へ渡す。 -/
def SingleRelativeComparison.ofCanonicalFirstRowSimplices (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient d.projection n))) :
    SingleRelativeComparison d :=
  SingleRelativeComparison.ofFirstRowSimplices d hq (verdierCanonicalKernelSquareIso d)

end SerrePositivity.KST.Fibration.Relative
