module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryLocalRestrictions
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquarePrecompositionCoherence

/-!
概要：任意の一単体の全局所 Hom 比較を、同じ境界比較と厳密に可換にする。
方針：分類先の単射境界制限で、元の指定自然性の path を持ち上げる。
規約：元の全局所比較への同型と、その境界での指定像を保持する。
使われ方：境界値を固定した任意の一単体の Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "R" => cocartesianOneBoundaryLocalSourceRestriction σ p q
local notation "T" => cocartesianOneBoundaryLocalTargetRestriction σ p q
local notation "S" => cocartesianStandardSimplexHomComparison σ p q
local notation "V" => cocartesianOneBoundaryHomComparison i σ p q

/-- 同じ境界の指定自然性の path を保持した厳密な正方形。 -/
def cocartesianOneBoundaryLocalHomCorrection :
    PathCorrectedFunctorSquare T S (R ≫ V)
      (cocartesianOneBoundaryHomComparison_localNaturalityIso i σ p q) :=
  pathCorrectedFunctorSquare T (kanEquivalenceLifting_of_kanFibration T) S (R ≫ V)
    (cocartesianOneBoundaryHomComparison_localNaturalityIso i σ p q)

/-- 同じ境界比較と厳密に可換な、元の全局所 Hom 比較の補正。 -/
def cocartesianOneBoundaryLocalCorrectedHom :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).map

/-- 補正した同じ作用は、指定境界比較と厳密に可換。 -/
lemma cocartesianOneBoundaryLocalCorrectedHom_comm :
    cocartesianOneBoundaryLocalCorrectedHom i σ p q ≫ T = R ≫ V :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).comm

/-- 同じ補正比較は元の全局所比較と指定同型で一致する。 -/
def cocartesianOneBoundaryLocalCorrectedHomIso :
    FunctorIso (cocartesianOneBoundaryLocalCorrectedHom i σ p q) S :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).exactComponentIso

/-- 同じ補正比較自体は、追加仮定なしに同値。 -/
lemma cocartesianOneBoundaryLocalCorrectedHom_isQCatEquivalence :
    IsQCatEquivalence (cocartesianOneBoundaryLocalCorrectedHom i σ p q) :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).map_isQCatEquivalence
    (cocartesianStandardSimplexHomComparison_isQCatEquivalence σ p q)

/-- 補正同型の境界での像は、元の指定局所自然性そのもの。 -/
lemma cocartesianOneBoundaryLocalCorrectedHomIso_boundary :
    F2.functorIsoOfEq ((cocartesianOneBoundaryLocalCorrectedHomIso i σ p q).postcomp T)
      (cocartesianOneBoundaryLocalCorrectedHom_comm i σ p q) rfl =
      cocartesianOneBoundaryHomComparison_localNaturalityIso i σ p q :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories
