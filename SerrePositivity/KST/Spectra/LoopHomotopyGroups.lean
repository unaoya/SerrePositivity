module

public import SerrePositivity.KST.Spectra.LoopPathFiber
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ContractibleTotalSequence

/-!
概要：Kan 複体の loop の正次数のホモトピー群の次数移動。
方針：実際の path fiber と収縮から長完全列の連結準同型を同型にする。
規約：このファイルでは loop の正次数を扱い、零次数の比較は別途扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）、BF 1978 §2。スペクトルの段の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan な標的の path space の正次数のホモトピー群は一元群。
方針：全自然数次数のホモトピー類の一元性を群の添字へ移す。
規約：添字 n は実際の次数 n + 1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。連結準同型の全単射性。 -/
instance basedPathSpace_group_subsingleton (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (basedPathSpace Y).right n (basedPathSpace Y).basepoint) :=
  inferInstanceAs (Subsingleton
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (basedPathSpace Y).right (n + 1) (basedPathSpace Y).basepoint))

/-- 概要：loop の正次数のホモトピー群は標的の一つ上の次数と同型。
方針：loop の fiber 同型、path の連結同型、基点の等式を合成する。
規約：π_(n+1)(ΩY) と π_(n+2)(Y) の群同型。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）、BF 1978 §2。 -/
def loopPositiveHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1) Y.basepoint :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (loopBasedPathFiberIso Y)
    (loopBasedPathFiberIso_basepoint Y)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHomEquivOfTotalSubsingleton (pathEndpoint Y).right
      (basedPathSpace Y).basepoint n).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl Y.right) (pathEndpoint_basepoint Y)))

end

end SerrePositivity.KST.Spectra
