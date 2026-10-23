module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryDiagramComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryLocalOriginal
public import SerrePositivity.InfinityCategories.F1.Cocartesian.HornBoundaryDiagramPullbacks

/-!
概要：任意の二単体の欠けた面を、同じ共有境界上の比較と厳密に揃える。
方針：一次元の指定 path を保つ補正を、元の二単体の中間面に適用する。
規約：底への二単体写像の単射性を要求せず、元の全 Hom と指定同型を保持する。
使われ方：任意の底の二次元境界を面とホーンから貼り合わせる。
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
variable {C : Type u} [Category.{u} C] (j : Fin 2)
  (σ : (Δ[2] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ

/-- 元の二単体の中間面に対する、同じ境界固定補正。 -/
def cocartesianTwoBoundaryLocalFaceComparison :=
  cocartesianOneBoundaryLocalCorrectedHom j τ p q

/-- 同じ面から共有境界への元の native 制限。 -/
def cocartesianTwoBoundaryLocalFaceNativeRestriction :=
  cocartesianOneBoundaryLocalSourceRestriction τ p q

/-- 同じ面から共有境界への元の分類先の制限。 -/
def cocartesianTwoBoundaryLocalFaceTargetRestriction :=
  cocartesianOneBoundaryLocalTargetRestriction τ p q

/-- 任意の二単体で、共有境界の同じ比較と厳密に可換。 -/
lemma cocartesianTwoBoundaryLocalFaceComparison_comm :
    cocartesianTwoBoundaryLocalFaceComparison j σ p q ≫
      cocartesianTwoBoundaryLocalFaceTargetRestriction σ p q =
    cocartesianTwoBoundaryLocalFaceNativeRestriction σ p q ≫
      cocartesianOneBoundaryDiagramComparison j τ p q :=
  cocartesianOneBoundaryLocalCorrectedHom_comm_diagram j τ p q

/-- 同じ補正比較は、任意の二単体で追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryLocalFaceComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoBoundaryLocalFaceComparison j σ p q) :=
  cocartesianOneBoundaryLocalCorrectedHom_isQCatEquivalence j τ p q

instance cocartesianTwoBoundaryLocalFaceNativeRestriction_fibration :
    Fibration (cocartesianTwoBoundaryLocalFaceNativeRestriction σ p q) :=
  cocartesianOneBoundaryLocalSourceRestriction_fibration τ p q

instance cocartesianTwoBoundaryLocalFaceTargetRestriction_fibration :
    Fibration (cocartesianTwoBoundaryLocalFaceTargetRestriction σ p q) :=
  cocartesianOneBoundaryLocalTargetRestriction_fibration τ p q

/-- 同じ面の補正比較は、元の大域全 Hom の作用を指定同型で回収する。 -/
def cocartesianTwoBoundaryLocalFaceComparison_originalIso :=
  cocartesianOneBoundaryLocalCorrectedHom_originalIso j τ p q

/-- 補正同型の共有境界での像は、元の指定局所自然性そのもの。 -/
lemma cocartesianTwoBoundaryLocalFaceComparison_iso_boundary :
    F2.functorIsoOfEq
      ((cocartesianOneBoundaryLocalCorrectedHomIso j τ p q).postcomp
        (cocartesianTwoBoundaryLocalFaceTargetRestriction σ p q))
      (cocartesianOneBoundaryLocalCorrectedHom_comm j τ p q) rfl =
      cocartesianOneBoundaryHomComparison_localNaturalityIso j τ p q :=
  cocartesianOneBoundaryLocalCorrectedHomIso_boundary j τ p q

end SerrePositivity.InfinityCategories
