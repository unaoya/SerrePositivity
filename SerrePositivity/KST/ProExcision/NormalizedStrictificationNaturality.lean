module
public import SerrePositivity.KST.ProExcision.LinearizedEndpointChainNaturality

/-!
# 厳密化の正規化鎖ホモトピーの自然性

概要：厳密化への全区間比較が可換な正方形を持つと、正規化鎖ホモトピーも自然。
方針：構成済みの線形区間からの正規化鎖ホモトピーの自然性を使う。
規約：KST Construction A.5、因子内の区間写像に適用する。
使われ方：同変な厳密化比較を二因子の全テンソルへ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial

/-- 概要：厳密化への全比較の正規化鎖ホモトピーは自然な区間の正方形を保つ。
方針：区間からの正規化比較の成分の自然性に帰着する。
規約：KST A.5、実区間の同変性から鎖比較の同変性を導く。
使われ方：Construction A.5 の因子内の二つの全比較。 -/
lemma normalizedStrictificationHomotopy_square
    {X X' Y Y' : SSet.{u}}
    {f e : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y}
    {f' e' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y'} {m m' : ℕ}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f e m) (h' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f' e' m')
    (a : X ⟶ X') (b : Y ⟶ Y')
    (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫ h'.strictificationHomotopy.h =
        h.strictificationHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b) :
    ChainHomotopySquare ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap a))
      ((normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap b))
      h.normalizedStrictificationHomotopy h'.normalizedStrictificationHomotopy := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalizedStrictificationHomotopy]
  apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
  apply ChainHomotopySquare.trans
  · exact normalizedLinearizedEndpointHomotopy_square h.strictificationHomotopy.h
      h'.strictificationHomotopy.h a b hh
  · apply ChainHomotopySquare.ofEq

end SerrePositivity.KST.ProExcision
