module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSmashUnit
public import SerrePositivity.KST.Spectra.SuspensionLoop

/-! # 元の円と単位を保つ suspension の前向き比較
概要：写した値の suspension から suspension の像へ、同じ円の単位を使って比較する。
方針：円の単位と元の smash 比較を合成し、元の商射と単位の回収を照合する。
規約：単射性や自然な逆は要求しない。使われ方：Ex∞ 後の BF 構造射の span。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の同じ点つき単体的円を、標準点つき対象として保持する。 -/
def pointedSSetCircleObject : PointedSSetObject.{u} := ⟨PointedSimplicialSet.circle.{u}⟩

/-- 元の円との同じ smash による、標準点つき suspension 対象。 -/
def pointedSSetSuspensionObject (X : PointedSSetObject.{u}) : PointedSSetObject.{u} :=
  pointedSSetSmashObject pointedSSetCircleObject X

/-- 元の円の単位と smash 比較から得る、同じ写した値の suspension の実比較。 -/
def coaugmentedPointedSuspensionComparison (X : PointedSSetObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (coaugmentedPointedObject F η X).obj ⟶
      (coaugmentedPointedObject F η (pointedSSetSuspensionObject X)).obj :=
  ((show pointedSSetCircleObject.obj ⟶
      (coaugmentedPointedObject F η pointedSSetCircleObject).obj from
        coaugmentedPointedUnit F η pointedSSetCircleObject) ⊗ₘ
      𝟙 (coaugmentedPointedObject F η X).obj) ≫
    coaugmentedPointedSmashMap F η pointedSSetCircleObject X

/-- 元の単位の suspension を、同じ元の円を固定した通常の点つき射として保持する。 -/
def coaugmentedPointedSuspensionUnit (X : PointedSSetObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (coaugmentedPointedObject F η X).obj :=
  PointedSimplicialSet.circle.{u} ◁
    (show X.obj ⟶ (coaugmentedPointedObject F η X).obj from coaugmentedPointedUnit F η X)

/-- 元の円と写した値の直積上では、元の単位・乗法比較・smash 商を回収する。 -/
lemma coaugmentedPointedSuspensionComparison_quotient (X : PointedSSetObject.{u}) :
    PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u}
      (coaugmentedPointedObject F η X).obj ≫
      (coaugmentedPointedSuspensionComparison F η X).right =
    (η.app PointedSimplicialSet.circle.{u}.right ⊗ₘ 𝟙 (F.obj X.obj.right)) ≫
      μ F PointedSimplicialSet.circle.{u}.right X.obj.right ≫
        F.map (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X.obj) := by
  have h := PointedSimplicialSet.productToSmash_naturality
    (show pointedSSetCircleObject.obj ⟶
      (coaugmentedPointedObject F η pointedSSetCircleObject).obj from
        coaugmentedPointedUnit F η pointedSSetCircleObject)
    (𝟙 (coaugmentedPointedObject F η X).obj)
  change _ ≫ (_ ≫ coaugmentedPointedSmashMap F η pointedSSetCircleObject X).right = _
  erw [Under.comp_right, ← Category.assoc, ← h, Category.assoc,
    coaugmentedPointedSmashMap_quotient]
  rfl

/-- 元の値の suspension の単位は、元の単位の suspension と比較の合成と一致する。 -/
lemma coaugmentedPointedSuspensionComparison_unit (X : PointedSSetObject.{u}) :
    coaugmentedPointedSuspensionUnit F η X ≫ coaugmentedPointedSuspensionComparison F η X =
    (show (pointedSSetSuspensionObject X).obj ⟶
      (coaugmentedPointedObject F η (pointedSSetSuspensionObject X)).obj from
        coaugmentedPointedUnit F η (pointedSSetSuspensionObject X)) := by
  change _ ≫ ((_ ⊗ₘ 𝟙 _) ≫ coaugmentedPointedSmashMap F η pointedSSetCircleObject X) = _
  erw [coaugmentedPointedSuspensionUnit, ← Category.assoc,
    tensorHom_id, ← tensorHom_def']
  exact coaugmentedPointedSmashMap_unit F η pointedSSetCircleObject X

end SerrePositivity.KST.SConstruction
