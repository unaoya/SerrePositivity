module

public import SerrePositivity.Archive.KST.DescentConditional.DisjointFamilyCechWeak
public import SerrePositivity.KST.Descent.FiniteCoproductZariskiCover

/-!
# 公理 (1) から有限非交和の値の比較を導く

## 概要
有限 Zariski 被覆族の実降下から、有限非交和上の値と成分の値の積の指定比較の弱同値を証明する。

## 方針
実際の成分の被覆に公理 (1) を適用し、各 Čech 段の対角比較の弱同値を使う。
比較先の定数図式の実降下と元の指定増強の可換性から、元の基底の比較を反映する。

## 規約
前層の有限非交和保存を追加の公理にしない。現時点の実際の空間値の比較で述べる。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 と (3.8) の有限非交和の値の同定。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen
open scoped Simplicial

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：有限非交和の値から各成分の値の積への指定比較は弱同値（公理 (1)、(3.8)）。
方針：実際の成分被覆の降下、対角比較の全段の弱同値、定数図式の実降下を比較する。
規約：有限非交和保存を前提にせず公理 (1) から導く。使われ方：局所 rank の非交和の値の比較。 -/
theorem zariskiFiniteCoproductComparison_weak
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    {ι : Type u} [Finite ι] (X : ι → FiniteTypeSchemes S)
    (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ SSet.{0}) [FiniteZariskiCechDescent I J F] :
    weakEquivalences SSet.{0} (familyProductComparison X (fun i ↦ Sigma.ι X i) F) := by
  have hA : HasCechSpaceDescent SimplexCategory I J
      (familyCechSpace X (fun i ↦ Sigma.ι X i) F) :=
    FiniteZariskiCechDescent.descent (I := I) (J := J) (F := F)
      (finiteCoproductZariskiCover X)
  have hB := constantAugmentedCechSpace_descent SimplexCategory I J
    ⦋0⦌ SimplexCategory.isTerminalZero hcof (∏ᶜ fun i ↦ F.obj (op (X i)))
  exact cechSpaceMap_left_weak_of_descent SimplexCategory I J
    (familyCechToConstantProduct X (fun i ↦ Sigma.ι X i) F) hA hB
    (disjointFamilyCechDiagonalProjection_weak I J hcof X F)

end SerrePositivity.KST.Descent
