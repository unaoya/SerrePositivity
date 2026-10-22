module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspension
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSmashNaturality
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedFunctorialMaps

/-! # 同じ suspension 比較の通常射に関する自然性
概要：円を固定した前向き比較は、同じ元の通常の点つき射と厳密に可換する。
方針：元の円の単位を移動し、元の smash 比較の両変数自然性を使う。
規約：全族自然性は別に接続する。使われ方：BF の前向き span の通常射の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の同じ通常射の suspension を、標準点つき対象間の射として保持する。 -/
def pointedSSetSuspensionMap {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    pointedSSetSuspensionObject X ⟶ pointedSSetSuspensionObject Y :=
  PointedSimplicialSet.circle.{u} ◁ (show X.obj ⟶ Y.obj from f)

/-- 同じ前向き suspension 比較は、元の通常の点つき射について厳密に自然。 -/
lemma coaugmentedPointedSuspensionComparison_naturality {X Y : PointedSSetObject.{u}}
    (f : X ⟶ Y) :
    (PointedSimplicialSet.circle.{u} ◁
      (show (coaugmentedPointedObject F η X).obj ⟶ (coaugmentedPointedObject F η Y).obj from
        coaugmentedPointedMap F η f)) ≫ coaugmentedPointedSuspensionComparison F η Y =
    coaugmentedPointedSuspensionComparison F η X ≫
      (show (coaugmentedPointedObject F η (pointedSSetSuspensionObject X)).obj ⟶
        (coaugmentedPointedObject F η (pointedSSetSuspensionObject Y)).obj from
          coaugmentedPointedMap F η (pointedSSetSuspensionMap f)) := by
  have h := coaugmentedPointedSmashMap_naturality F η (𝟙 pointedSSetCircleObject) f
  rw [coaugmentedPointedMap_id] at h
  change (_ ◁ _) ≫ ((_ ⊗ₘ 𝟙 _) ≫ _) = (_ ⊗ₘ 𝟙 _) ≫ _ ≫ _
  erw [tensorHom_id, ← Category.assoc, whisker_exchange, Category.assoc]
  exact congrArg (fun q =>
    (show pointedSSetCircleObject.obj ⟶
      (coaugmentedPointedObject F η pointedSSetCircleObject).obj from
        coaugmentedPointedUnit F η pointedSSetCircleObject) ▷
          (coaugmentedPointedObject F η X).obj ≫ q) h

end SerrePositivity.KST.SConstruction
