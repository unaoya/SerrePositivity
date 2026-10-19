module
public import SerrePositivity.KST.SConstruction.StableModelEquivalences
public import SerrePositivity.KST.SConstruction.CutRelativeEquivalence
public import SerrePositivity.KST.SConstruction.CutIntervalEquivalences

/-! # 切断の同値の完全な逆データ
概要：相対切断および左右の短い区間の同値を完全関手の逆データとして束ねる。
方針：既に構成した逆関手と内部の関手同型をそのまま用いる。
規約：追加の逆関手存在仮定を置かない。使われ方：反復実現の同値保存の適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 相対切断比較の完全な逆データ。 -/
def cutRelativeStableEquivalence (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    StableModelEquivalence (sStableModel n X)
      (relativeCofiberStableModel (cutLeftSupport n k X) (cutRightSupport n k X)) where
  hom := cutRelativeComparison n k X
  inv := cutRelativeMiddle n k X
  homInvIso := (cutRelativeEquivalence n k X).homInvIso
  invHomIso := cutRelativeMiddle_comparisonIso n k X

/-- 左側支持部分圏から短い区間への制限の完全な逆データ。 -/
def cutLeftIntervalStableEquivalence (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    StableModelEquivalence (closedStableModel (cutLeftSupport n k X)) (sStableModel k.val X) where
  hom := cutLeftIntervalRestriction n k X
  inv := cutLeftIntervalExtension n k X
  homInvIso := cutLeftInterval_restriction_extensionIso n k X
  invHomIso := (cutLeftIntervalEquivalence n k X).invHomIso

/-- 右側支持部分圏から短い区間への制限の完全な逆データ。 -/
def cutRightIntervalStableEquivalence (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    StableModelEquivalence (closedStableModel (cutRightSupport n k X))
      (sStableModel (n - k.val) X) where
  hom := cutRightIntervalRestriction n k X
  inv := cutRightIntervalExtension n k X
  homInvIso := cutRightInterval_restriction_extensionIso n k X
  invHomIso := (cutRightIntervalEquivalence n k X).invHomIso

end SerrePositivity.KST.SConstruction
