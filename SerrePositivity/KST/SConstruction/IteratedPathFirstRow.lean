module
public import SerrePositivity.KST.SConstruction.StablePathFirstRow
public import SerrePositivity.KST.SConstruction.MultiSTrivialFibration

/-! # 経路の第一行比較への有限反復 S の適用
概要：経路の比較に外側の有限反復 S と core の実現を適用し、対角の弱同値を得る。
方針：安定な入力の圏の比較と、自明ファイブレーションの反復による保存を使う。
規約：経路は最内側、r 個の S がその外側。使われ方：反復の経路と第一行の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：経路の各段の外側に r 重の S を施して core の対角を取った図式。
方針：安定な経路図式に反復実現の関手を後合成する。
規約：経路方向は最内側。使われ方：反復した経路比較の源。 -/
def iteratedPathRealizationDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u} :=
  stableSPathDiagram X ⋙ multiRealizationFunctor r

/-- 概要：第一行の各関手圏の外側に r 重の S を施した core の実現図式。
方針：安定な第一行図式に反復実現の関手を後合成する。
規約：残りの r 方向と core の次数は対角にする。使われ方：反復した比較の標的。 -/
def iteratedFirstRowRealizationDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u} :=
  stablePathFirstRowDiagram X ⋙ multiRealizationFunctor r

/-- 概要：経路の第一行比較に有限反復 S の core の実現を適用した自然変換。
方針：安定な入力の比較を反復実現の関手で後合成する。
規約：全ての経路方向の単体作用素について自然。使われ方：対角比較の入力。 -/
def iteratedPathFirstRowComparison (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealizationDiagram r X ⟶ iteratedFirstRowRealizationDiagram r X :=
  Functor.whiskerRight (stablePathFirstRowRestriction X) (multiRealizationFunctor r)

/-- 概要：反復した第一行比較の各経路次数の射は局所化で可逆。
方針：各成分の自明ファイブレーションを反復実現で写す定理を使う。
規約：各反復実現の Kan 性は要求しない。使われ方：全対角の弱同値。 -/
lemma iteratedPathFirstRowComparison_app_localized_isIso (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((iteratedPathFirstRowComparison r X).app d)) :=
  multiRealizationFunctor_map_localized_isIso r ((stablePathFirstRowRestriction X).app d)

/-- 概要：全方向を対角に取った反復経路の実現。
方針：経路次数も既に反復実現した core の次数と対角にする。
規約：次数 n の各 S 方向は n、最内側の経路の S は n+1。使われ方：反復の経路全空間。 -/
def iteratedPathRealization (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (iteratedPathRealizationDiagram r X)

/-- 概要：全方向を対角に取った反復した第一行の core の実現。
方針：第一行次数と残りの反復方向・core の次数を同時に対角にする。
規約：Fun(N([n]),X) に外側の r 重 S を施す模型。使われ方：経路全空間との比較。 -/
def iteratedFirstRowRealization (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (iteratedFirstRowRealizationDiagram r X)

/-- 概要：有限反復 S の適用後の経路と第一行の全対角の比較。
方針：構成済みの自然変換を対角実現で写す。
規約：弱同値性は次の定理で示す。使われ方：反復経路の fiber 比較への接続。 -/
def iteratedPathFirstRowDiagonalComparison (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ iteratedFirstRowRealization r X :=
  simplicialDiagonalFunctor.map (iteratedPathFirstRowComparison r X)

/-- 概要：有限反復 S の適用後の経路と第一行の全対角の比較は局所化で可逆。
方針：経路次数ごとの弱同値と対角の比較定理を使う。
規約：全対角を Kan と仮定しない。使われ方：反復した経路の自然な弱同値。 -/
lemma iteratedPathFirstRowDiagonalComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (iteratedPathFirstRowDiagonalComparison r X)) :=
  SerrePositivity.BisimplicialModel.localized_diagonal_map (iteratedPathFirstRowComparison r X)
    (iteratedPathFirstRowComparison_app_localized_isIso r X)

/-- 概要：反復後の経路の零次比較も、反復により写した既存の S₁ 比較を回収する。
方針：安定な入力の零次比較の合成式を反復実現の関手で写す。
規約：経路は最内側の S₁。使われ方：反復後の一次方向の比較との照合。 -/
lemma iteratedPathFirstRowComparison_zero (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathFirstRowComparison r X).app (Opposite.op ⦋0⦌) ≫
        (multiRealizationFunctor r).map (stablePathFirstRowZeroComparison X) =
      (multiRealizationFunctor r).map (stableSOneComparison X) := by
  change (multiRealizationFunctor r).map ((stablePathFirstRowRestriction X).app (Opposite.op ⦋0⦌)) ≫
    (multiRealizationFunctor r).map (stablePathFirstRowZeroComparison X) = _
  rw [← CategoryTheory.Functor.map_comp, stablePathFirstRowRestriction_zero]

end SerrePositivity.KST.SConstruction
