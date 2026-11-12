module
public import SerrePositivity.KST.SConstruction.StableOneDirectionBoundaryAction
public import SerrePositivity.KST.SConstruction.OneDirectionReduction
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionLaws
public import SerrePositivity.KST.SConstruction.PointedEnrichedActionFunctor

/-!
概要：元の一次方向の境界商へ、全自然同値族の作用を降ろす。
方針：保存済みの全零境界を同じ商で崩し、その普遍性に沿って降下する。
規約：元の商と基点を保持する。使われ方：有限 native BF 四角形の隣接段 span。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open InfinityCategories LocalizingInvariants Spectra

/-- 概要：元の境界全体は同じ商の基点へ送られる。
方針：境界への制限作用と商射の崩壊式を使う。
規約：全パラメータの等式。使われ方：商作用の降下条件。 -/
lemma stableOneDirectionReducedAction_collapse (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((oneDirectionFatBoundary (r + 1) (stableCategoryModel C)).ι ▷
        (C ⟶[SSet.{u}] D)) ≫ stableOneDirectionAction (r + 1) C D ≫
      oneDirectionReductionQuotient r (stableCategoryModel D) =
        toUnit _ ≫ (oneDirectionReducedRealization r (stableCategoryModel D)).hom :=
  boundaryFamily_collapse _ _ _ (stableOneDirectionBoundaryAction (r + 1) C D)
    (stableOneDirectionBoundaryAction_inclusion (r + 1) C D)

/-- 概要：元の一次方向商への全高次入力族の作用。
方針：同じ境界商の普遍的降下を使う。
規約：基点を選び直さない。使われ方：隣接段比較の点つき作用。 -/
def stableOneDirectionReducedAction (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (oneDirectionReducedRealization r (stableCategoryModel C)).right ⊗
      (C ⟶[SSet.{u}] D) ⟶
        (oneDirectionReducedRealization r (stableCategoryModel D)).right :=
  cofiberFamilyDescRaw (oneDirectionFatBoundary (r + 1) (stableCategoryModel C)).ι
    (oneDirectionReducedRealization r (stableCategoryModel D))
    (stableOneDirectionAction (r + 1) C D ≫
      oneDirectionReductionQuotient r (stableCategoryModel D))
    (stableOneDirectionReducedAction_collapse r C D)

/-- 概要：商射に沿って元の全作用を回収する。
方針：普遍的降下の商射への制限式を使う。
規約：全単体の厳密等号。使われ方：元の S₁ 比較との照合。 -/
lemma stableOneDirectionReducedAction_quotient (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (oneDirectionReductionQuotient r (stableCategoryModel C) ▷
        (C ⟶[SSet.{u}] D)) ≫ stableOneDirectionReducedAction r C D =
      stableOneDirectionAction (r + 1) C D ≫
        oneDirectionReductionQuotient r (stableCategoryModel D) :=
  cofiberFamilyDescRaw_quotient _ _ _ _

/-- 概要：全入力族は元の商の基点を固定する。
方針：同じ降下の基点脚への制限を使う。
規約：全時刻での等式。使われ方：標準点つき豊穣への包装。 -/
lemma stableOneDirectionReducedAction_basepoint (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((oneDirectionReducedRealization r (stableCategoryModel C)).hom ▷
        (C ⟶[SSet.{u}] D)) ≫ stableOneDirectionReducedAction r C D =
      toUnit _ ≫ (oneDirectionReducedRealization r (stableCategoryModel D)).hom :=
  cofiberFamilyDescRaw_basepoint _ _ _ _

/-- 概要：同じ全作用を基点固定 Hom への族として保持する。
方針：同じ商の basedHom への普遍的降下を使う。
規約：同じ全パラメータを保持する。使われ方：点つき厳密豊穣作用。 -/
def stableOneDirectionReducedFamilyMap (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (C ⟶[SSet.{u}] D) ⟶
      (PointedObject.basedHom
        (oneDirectionReducedRealization r (stableCategoryModel C))
        (oneDirectionReducedRealization r (stableCategoryModel D))).right :=
  cofiberFamilyDesc (oneDirectionFatBoundary (r + 1) (stableCategoryModel C)).ι
    (oneDirectionReducedRealization r (stableCategoryModel D))
    (stableOneDirectionAction (r + 1) C D ≫
      oneDirectionReductionQuotient r (stableCategoryModel D))
    (stableOneDirectionReducedAction_collapse r C D)

/-- 概要：Hom 包含後には元の全作用の curry を回収する。
方針：basedHom の等化子への包含式を使う。
規約：同じ作用を固定する。使われ方：比較自然性の反映。 -/
lemma stableOneDirectionReducedFamilyMap_inclusion (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableOneDirectionReducedFamilyMap r C D ≫
      PointedObject.basedHomι
        (oneDirectionReducedRealization r (stableCategoryModel C))
        (oneDirectionReducedRealization r (stableCategoryModel D)) =
      curry (stableOneDirectionReducedAction r C D) := Limits.equalizer.lift_ι _ _

end SerrePositivity.KST.SConstruction
