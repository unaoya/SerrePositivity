module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：同じ resolved 商上の中央射の両射影を全 dg 関手として回収する。
方針：元二実像小模型の実逆回転の射影公式を特殊化する。
規約：対象別の同型だけで代用しない。native 全比較は別工程。
使われ方：固定 S 長方形の中央辺の二脚照合。
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
local notation "T" => DGPerfectComparisonBase R (Q) (F) (G)
local notation "I" => DGFunctor.id (T)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "M" => dgHomGluingBimodule R (U) (U) (U) (DGFunctor.id (U)) (DGFunctor.id (U))

/-- 概要：中央射の左射影は元比較の同じ実逆 shift cone 関手。
方針：元の厳密な全 dg 射影公式を適用する。規約：同じ resolved 商を保持。
使われ方：右面の第一成分照合。 -/
lemma dgOdotMilnorRightAxisLift_left :
    (dgOdotMilnorRightAxisLift R d).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (U) (U) (M)) =
      (dgPerfectComparisonHomGluingFunctor R (Q) (F) (G) (τ)).comp
        (dgHomGluingLoopConeSmall R (T) (T) (T) (I) (I)) :=
  dgPerfectComparisonInverseRotationFunctor_left R (Q) (F) (G) (τ)

/-- 概要：中央射の右射影は元比較の同じ指定二重 shift 成分。
方針：元の厳密な全 dg 射影公式を適用する。規約：同じ resolved 商を保持。
使われ方：右面の第二成分照合。 -/
lemma dgOdotMilnorRightAxisLift_right :
    (dgOdotMilnorRightAxisLift R d).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (U) (U) (M)) =
      (dgPerfectComparisonHomGluingFunctor R (Q) (F) (G) (τ)).comp
        (dgHomGluingLoopConeShiftedTarget R (T) (T) (T) (I) (I)) :=
  dgPerfectComparisonInverseRotationFunctor_right R (Q) (F) (G) (τ)

end SerrePositivity.KST.SConstruction
