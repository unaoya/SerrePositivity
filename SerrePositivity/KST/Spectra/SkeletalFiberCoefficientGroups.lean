module

public import SerrePositivity.KST.Spectra.SkeletalFiberFunctions
public import SerrePositivity.KST.Spectra.SimplexCellHomotopyGroups

/-!
概要：骨格の塔の fiber の正次数群は非退化単体を添字とする高次係数群の関数群。
方針：セルの Hom の関数表示、球面の次数移動、セルの添字の同値を合成する。
規約：塔の境界準同型や微分の式はこの同型だけから主張しない。
使われ方：Goerss–Jardine VIII §1。塔から群 cochain への群としての係数表示。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：n 段の fiber の π_(r+1) は非退化 n+1 単体上の π_(n+r+2) 係数の関数群。
方針：セルごとの写像空間の群同型へ次数移動と添字の同値を適用する。
規約：K の Kan 性は不要。係数 X の Kan 性を要求する。
使われ方：Goerss–Jardine VIII §1。正規化された cochain の群の入力。 -/
def stageFiberCoefficientEquiv (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right r
        (UnbasedPointedMapping.stageFiber K X n).basepoint ≃*
      (K.nonDegenerate (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right (n + 1 + r) X.basepoint) :=
  (stageFiberFunctionHomotopyEquiv K X n r).trans
    (MulEquiv.arrowCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)) (SimplexCell.positiveHomotopyEquiv X n r))

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
