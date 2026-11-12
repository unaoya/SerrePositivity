module
public import SerrePositivity.KST.Fibration.Relative.ConnectiveInterface
public import SerrePositivity.KST.Fibration.RelativeFirstRowSimplexQuotient

/-!
概要：Sp の標準単体商比較を、K-B2 の同じ相対実現の二比較へ渡す。
方針：標準単体座標から元の正段比較へ戻し、既存の供給境界を構成する。
規約：商比較と全四角形同型は明示入力のまま保持し、存在は主張しない。
使われ方：K-6 c4・c5 の供給を b の SingleRelativeComparison へ代入する入口。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：同じ商の全標準単体比較と指定全四角形同型を相対実現界面へ接続する。
方針：同じ厳密座標四角形による可逆性の同値を各正段に適用する。
規約：零次元の標準単体も含め、元の商射・全四角形同型を保持する。
使われ方：Sp の c5 供給と S-1 (a) による c4 を b・d の既存消費側へ渡す。 -/
def SingleRelativeComparison.ofFirstRowSimplices (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient d.projection n)))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection)) :
    SingleRelativeComparison d :=
  SingleRelativeComparison.ofPositiveStages d
    (fun n => (relativeSQuotient_localized_isIso_iff_firstRowSimplex d.projection n).mpr
      (hq n)) e

end SerrePositivity.KST.Fibration.Relative
