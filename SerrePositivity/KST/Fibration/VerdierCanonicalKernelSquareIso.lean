module
public import SerrePositivity.KST.Fibration.VerdierMovingCanonicalFiniteExt

/-!
概要：元の Verdier 四角形から同じ相対 S• 商核四角形への全関手同型。
方針：実読出し・境界を固定した相対合成の存在定理を四有限端点比較へ代入する。
規約：四角形以外の入力は取らず、有限端点や外延性の存在仮定を残さない。
使われ方：K-6 c4 の完成した比較を c5・b の元の商実現へ渡す。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：同じ元の全 S• 四角形と実商核四角形の無条件の全関手同型。
方針：供給済みの実読出しと実相対合成を選び、S-1 (a) の消費側へ渡す。
規約：指定二胞体・四辺を含む全四角形を保ち、商実現比較は要求しない。
使われ方：c5 の標準単体商比較だけを残す SingleRelativeComparison の構成。 -/
def verdierCanonicalKernelSquareIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection) := by
  let L := Classical.choose (verdierLowerNativeReadoutRecovery_exists d)
  have hL := Classical.choose_spec (verdierLowerNativeReadoutRecovery_exists d)
  let H := Classical.choose (verdierReadoutRelativeComposition_exists d L hL.2 hL.1)
  have hH := Classical.choose_spec (verdierReadoutRelativeComposition_exists d L hL.2 hL.1)
  exact kbMovingCanonicalFiniteExtConsumer d L hL.2 hL.1 H
    (Classical.choose hH) (Classical.choose_spec hH)

end SerrePositivity.KST.Fibration
