module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornSharedCorrection
public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryLocalCorrection
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundarySharedComparison

/-!
概要：二次元境界の欠けた一次元面の比較を、同じ共有境界比較と厳密に可換にする。
方針：任意の一次元セルに対する既存の補正比較を、その同じ面へ適用する。
規約：元の全局所 Hom と同じ指定境界比較を保持する。
使われ方：ホーン側の補正と境界全体へ貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 欠けた面の同じ共有境界を固定した補正比較。 -/
def cocartesianTwoBoundaryFaceComparison := cocartesianOneBoundaryLocalCorrectedHom j τ p q

/-- 同じ欠けた面から共有境界への native 制限。 -/
def cocartesianTwoBoundaryFaceNativeRestriction :=
  cocartesianOneBoundaryLocalSourceRestriction τ p q

/-- 同じ欠けた面から共有境界への分類先の制限。 -/
def cocartesianTwoBoundaryFaceTargetRestriction :=
  cocartesianOneBoundaryLocalTargetRestriction τ p q

/-- 同じ補正比較は、ホーンと共有する境界比較と厳密に可換。 -/
lemma cocartesianTwoBoundaryFaceComparison_comm :
    cocartesianTwoBoundaryFaceComparison j p q ≫
      cocartesianTwoBoundaryFaceTargetRestriction p q =
    cocartesianTwoBoundaryFaceNativeRestriction p q ≫
      cocartesianOneBoundaryDiagramComparison j τ p q :=
  cocartesianOneBoundaryLocalCorrectedHom_comm_diagram j τ p q

/-- 同じ欠けた面の補正比較は追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryFaceComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoBoundaryFaceComparison j p q) :=
  cocartesianOneBoundaryLocalCorrectedHom_isQCatEquivalence j τ p q

/-- 元の面の native 制限は Kan fibration。 -/
instance cocartesianTwoBoundaryFaceNativeRestriction_fibration :
    Fibration (cocartesianTwoBoundaryFaceNativeRestriction p q) :=
  cocartesianOneBoundaryLocalSourceRestriction_fibration τ p q

/-- 同じ分類先の面制限も Kan fibration。 -/
instance cocartesianTwoBoundaryFaceTargetRestriction_fibration :
    Fibration (cocartesianTwoBoundaryFaceTargetRestriction p q) :=
  cocartesianOneBoundaryLocalTargetRestriction_fibration τ p q

end SerrePositivity.InfinityCategories
