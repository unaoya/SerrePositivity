module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationRealizedCone
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：同じ resolved 商上の実逆回転 cone 比較成分を、元 Milnor 中央射へ特殊化する。
方針：保存済み二実 Perf 延長と元比較を、同じ実加群 cone・同じ二像評価へ渡す。
規約：逆回転基底の Yoneda 評価と全関手族の自然性は後続工程。
使われ方：三入力付き共通 S 長方形の指定上二単体の実比較成分。
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

/-- 概要：同じ元 Milnor 実逆回転 cone の二像評価後の指定比較射。
方針：同じ resolved 商・元二成分・元比較を特殊化する。
規約：元の実射を選び直さない。使われ方：実差の合成全比較の成分。 -/
abbrev dgOdotMilnorRightAxisRealizedConeComparison :=
  dgPerfectComparisonInverseRotationRealizedConeComparison R (Q) (F) (G) (τ)

/-- 概要：同じ元商評価後の指定比較成分は K(Q) で同値。
方針：実逆回転と同じ二像評価の同値判定を特殊化する。
規約：全比較や指定二単体の完成とは数えない。使われ方：後続全比較の成分認証。 -/
lemma dgOdotMilnorRightAxisRealizedConeComparison_isIso (x : P) :
    IsIso ((moduleToHomotopy R (Q)).map (dgOdotMilnorRightAxisRealizedConeComparison R d x)) :=
  dgPerfectComparisonInverseRotationRealizedConeComparison_isIso R (Q) (F) (G) (τ) x

end SerrePositivity.KST.SConstruction
