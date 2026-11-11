module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonalPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLiftingInvertible

/-!
概要：合成三角形の対角に沿う、任意のパラメーター全体の可逆輸送。
方針：既存の対角の持ち上げ性を内部 Hom に移し、指定終点の可逆辺を持ち上げる。
規約：Ind-S (9) のユーザー許可により、既存 KanEquivalenceLiftingFibration 経由の
F2/CatInfinity 推移 import のみを許可する。F2 と KST の直接 import はしない。
使われ方：長辺の全族の比較を三角形の全族へ持ち上げる。第一短辺の固定は別条件。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 任意の K 全体で、指定された対角の可逆辺を同じ終点の三角形族へ持ち上げる。
第一短辺も輸送されるため、固定内ホーンの fiber 内での輸送とは区別する。 -/
lemma controlledCompositionDiagonalFamily_transport
    {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
    {y z : X _⦋0⦌} (g : X.Edge y z) (K : SSet.{u})
    (t : ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g)) _⦋0⦌)
    (e : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e)))
    (ht : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm
      (((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g)).app (Opposite.op ⦋0⦌) t)) :
    ∃ l : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g),
      stdSimplex.δ (0 : Fin 2) ≫ l = SSet.yonedaEquiv.symm t ∧
      l ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g) = e ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv l)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting.invertibleTargetLifting
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanEquivalenceLifting_compositionCorrespondenceDiagonal x g) K) t e he ht

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
