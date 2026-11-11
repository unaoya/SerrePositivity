module
public import SerrePositivity.KST.SConstruction.DGFunctorNativeEvaluation
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisEndConeTriangle

/-!
概要：元実商上の右軸 cone 零化面を、native 全関手族の実二単体へ写す。
方針：元 Hom end 二単体を、全単体を保つ native 評価で運ぶ。
規約：core や各対象だけに制限しない。同じ元解像度・元実商・元比較を保持する。
使われ方：元 cone の全図式比較と固定 ν の実逆回転への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed Opposite DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))

/-- 概要：元右軸比較の指定 cone 零化を全 native 関手圏の実二単体にする。
方針：元全 end 二単体を同じ native 全評価で写す。
規約：元次数 −1 の自然零化を保持。使われ方：元 cofiber 全図式の零化面。 -/
def dgOdotMilnorRightAxisFullConeTriangle :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R (Q)))) _⦋2⦌ :=
  (dgFunctorNativeFullFamilyMap R (P) (RightModule R (Q))).app (op ⦋2⦌)
    (dgOdotMilnorRightAxisEndConeTriangle R d)

end SerrePositivity.KST.SConstruction
