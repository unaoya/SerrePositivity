module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.Spectra.Pointed.SmashPentagon
public import SerrePositivity.Spectra.Pointed.SmashHexagon
public import SerrePositivity.Spectra.Pointed.SmashTriangle
public import SerrePositivity.Spectra.Pointed.SmashAdjunction

/-!
# smash による閉対称モノイダル構造

構成済みの smash、零次球面、結合子、単位、交換を型クラスへ登録する。
pentagon・triangle・二つの hexagon は標準射の普遍性から証明済み。
等化子による基点付き内部 Hom と smash の随伴を閉構造へ接続する。
この構造は通常の圏での smash であり、導来 smash や安定モデル構造ではない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasFiniteColimits C]

/-- smash をテンソル積とするモノイダル構造のデータ。 -/
instance smashMonoidalCategoryStruct : MonoidalCategoryStruct (PointedObject C) where
  tensorObj := smash
  tensorHom := smashMap
  whiskerLeft X _ _ f := smashMap (𝟙 X) f
  whiskerRight f Y := smashMap f (𝟙 Y)
  tensorUnit := sphereZero
  associator := smashAssociator
  leftUnitor := smashLeftUnitor
  rightUnitor := smashRightUnitor

/-- 構成した結合・単位の整合性から得るモノイダル圏。 -/
instance smashMonoidalCategory : MonoidalCategory (PointedObject C) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := smashMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' ↦ smashMap_comp f g f' g')
    (associator_naturality := fun f g h ↦ smashAssoc_naturality f g h)
    (leftUnitor_naturality := fun f ↦ leftUnitHom_naturality f)
    (rightUnitor_naturality := fun f ↦ rightUnitHom_naturality f)
    (pentagon := smashAssoc_pentagon)
    (triangle := smashAssoc_triangle)

/-- smash の交換同型と hexagon による対称モノイダル構造。 -/
instance smashSymmetricCategory : SymmetricCategory (PointedObject C) where
  braiding := smashSymmetry
  braiding_naturality_right := by
    intro X Y Z f
    exact smashSwap_naturality (𝟙 X) f
  braiding_naturality_left := by
    intro X Y f Z
    exact smashSwap_naturality f (𝟙 Z)
  hexagon_forward := smashAssoc_hexagon_forward
  hexagon_reverse := smashAssoc_hexagon_reverse
  symmetry := smashSwap_comp

variable [HasEqualizers C]

/-- 基点付き内部 Hom を右随伴とする閉構造。 -/
instance smashMonoidalClosed : MonoidalClosed (PointedObject C) where
  closed X := {
    rightAdj := basedHomFunctor X
    adj := smashHomAdjunction X }

omit [HasEqualizers C] in
/-- 登録したテンソル積は、既存の通常の smash と定義上同じ。 -/
lemma tensorObj_eq_smash (X Y : PointedObject C) : X ⊗ Y = smash X Y := rfl

/-- 登録した内部 Hom は、等化子で構成した基点付き内部 Hom と同じ。 -/
lemma ihom_obj_eq_basedHom (X Y : PointedObject C) :
    (ihom X).obj Y = basedHom X Y := rfl

end SerrePositivity.PointedObject

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.8.2.14" (partial := component) "仮定：有限余極限と等化子をもつ通常の Cartesian 閉モノイダル圏の pointed objects（集合・単体集合の場合を含む）（Lean が強い：通常の Cartesian 閉モノイダル圏の場合）。結論：積から二つの軸を基点へ潰す smash を対称モノイダル積とし、基点付き内部 Hom を右随伴に持つ閉構造を構成する（この仮定での HA の結論の一部に一致）。pointed spaces の ∞ 圏への比較と、PrL の idempotent 性からの一意性は含まれない。"] _root_.SerrePositivity.PointedObject.smashMonoidalCategory
attribute [cite HA "4.8.2.14" (partial := component) "仮定：有限余極限と等化子をもつ通常の Cartesian 閉モノイダル圏の pointed objects（集合・単体集合の場合を含む）（Lean が強い：通常の Cartesian 閉モノイダル圏の場合）。結論：積から二つの軸を基点へ潰す smash を対称モノイダル積とし、基点付き内部 Hom を右随伴に持つ閉構造を構成する（この仮定での HA の結論の一部に一致）。pointed spaces の ∞ 圏への比較と、PrL の idempotent 性からの一意性は含まれない。"] _root_.SerrePositivity.PointedObject.smashMonoidalClosed
attribute [cite HA "4.8.2.14" (partial := component) "仮定：有限余極限と等化子をもつ通常の Cartesian 閉モノイダル圏の pointed objects（集合・単体集合の場合を含む）（Lean が強い：通常の Cartesian 閉モノイダル圏の場合）。結論：積から二つの軸を基点へ潰す smash を対称モノイダル積とし、基点付き内部 Hom を右随伴に持つ閉構造を構成する（この仮定での HA の結論の一部に一致）。pointed spaces の ∞ 圏への比較と、PrL の idempotent 性からの一意性は含まれない。"] _root_.SerrePositivity.PointedObject.smashSymmetricCategory
attribute [cite HA "4.8.2.14" (partial := component) "仮定：有限余極限と等化子をもつ通常の Cartesian 閉モノイダル圏の pointed objects（集合・単体集合の場合を含む）（Lean が強い：通常の Cartesian 閉モノイダル圏の場合）。結論：積から二つの軸を基点へ潰す smash を対称モノイダル積とし、基点付き内部 Hom を右随伴に持つ閉構造を構成する（この仮定での HA の結論の一部に一致）。pointed spaces の ∞ 圏への比較と、PrL の idempotent 性からの一意性は含まれない。"] _root_.SerrePositivity.PointedObject.tensorObj_eq_smash
