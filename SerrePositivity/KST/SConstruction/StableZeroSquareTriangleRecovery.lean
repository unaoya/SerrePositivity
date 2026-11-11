module
public import SerrePositivity.KST.SConstruction.StableZeroSquareComparison
public import SerrePositivity.KST.SConstruction.SpecifiedHomotopyRestriction

/-!
概要：元零四角形の全比較は元上下二胞体の指定全比較そのものを制限として持つ。
方針：元上面の厳密回収と、元下代表の全射の類の保持を使う。
規約：同型の存在だけへ弱めない。使われ方：全右面の指定三境界の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex f 0 1)))

/-- 概要：元全四角形比較の上二胞体制限は同じ元指定比較そのもの。
方針：同じ元上ホモトピーの厳密制限を元関手辺で回収する。
規約：元上比較を保持。使われ方：指定零側面の同時回収。 -/
lemma stableZeroSquareComparison_upper :
    (stableZeroSquareComparison H hz).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) =
      squareFrameTriangleComparison H 0 := by
  exact specifiedHomotopyRestrictionIso (stableZeroSquareHomotopy H hz)
    (stableZeroSquareComparison H hz) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) rfl rfl
    (squareFrameTriangleHomotopy H 0) (squareFrameTriangleComparison H 0) rfl
    (stableZeroSquareHomotopy_upper H hz)

/-- 概要：元全四角形比較の下二胞体制限は同じ元指定比較そのもの。
方針：共有対角だけを修正した代表の全類回収を使う。
規約：元下比較の全関手同型を保持。使われ方：指定包含・商側面の同時回収。 -/
lemma stableZeroSquareComparison_lower :
    (stableZeroSquareComparison H hz).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) =
      squareFrameTriangleComparison H 1 := by
  exact specifiedHomotopyRestrictionIso (stableZeroSquareHomotopy H hz)
    (stableZeroSquareComparison H hz) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) rfl rfl
    (squareFrameAlignedLowerTriangleHomotopy H hz) (squareFrameTriangleComparison H 1)
    (squareFrameAlignedLowerTriangleHomotopy_class H hz).symm
    (stableZeroSquareHomotopy_lower H hz)
end SerrePositivity.KST.SConstruction
