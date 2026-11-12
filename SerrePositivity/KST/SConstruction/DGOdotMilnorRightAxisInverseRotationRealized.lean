module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationRealized
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：同じ resolved 商上の実逆回転の二段 realization 全比較を元 Milnor 入力へ接続する。
方針：元二 Perf 関手と元比較の同じ全関手同型を特殊化する。
規約：元 cell 始域・元 resolved 商と元全 Hom を保持する。
使われ方：LT 実右面の全合成比較。固定 ν の三認証は別工程。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d

/-- 概要：同じ元 Milnor 実逆回転の二段 realization 全族。
方針：元 resolved 商上の元二実像小模型を保持する。
規約：元全 Hom と元 cell 始域を保持。使われ方：実全合成比較の始域。 -/
abbrev dgOdotMilnorRightAxisInverseRotationRealizedFamily :=
  dgPerfectComparisonInverseRotationRealizedFamily R (Q) (F) (G) (τ)

/-- 概要：同じ元 Milnor 実逆回転二段 realization から元第二 Perf 値への全比較。
方針：元全実逆回転・元指定厳密逆・同じ二段評価の全比較を使用する。
規約：商辺だけの関手同型や対象別の比較で代用しない。
使われ方：固定 ν の全実長方形と指定上下二単体への接続。 -/
def dgOdotMilnorRightAxisInverseRotationRealizedNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisInverseRotationRealizedFamily R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying R (Q) (G))) :=
  dgPerfectComparisonInverseRotationRealizedNerveComparison R (Q) (F) (G) (τ)
end SerrePositivity.KST.SConstruction
