module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedConstants
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlying

/-! # 同じ有限積保存関手による smash の前向き比較
概要：元の monoidal 比較と元の smash 商射から、写した点つき値の smash 比較を作る。
方針：両軸の像を定数写像として回収し、元の smash の普遍性で降ろす。
規約：比較の逆・単射性・弱同値性は仮定しない。使われ方：Ex∞ の suspension 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 同じ元の二つの点つき値の smash を標準点つき対象として保持する。 -/
def pointedSSetSmashObject (X Y : PointedSSetObject.{u}) : PointedSSetObject.{u} :=
  ⟨X.obj ⊗ Y.obj⟩

/-- 写した直積の第一軸は、元の smash 商の像の下で零になる。 -/
lemma coaugmentedPointedSmash_axisLeft (X Y : PointedSSetObject.{u}) :
    (PointedObject.axisLeft (coaugmentedPointedObject F η X).obj
      (coaugmentedPointedObject F η Y).obj).right ≫
      μ F X.obj.right Y.obj.right ≫ F.map (PointedSimplicialSet.productToSmash X.obj Y.obj) =
    toUnit (coaugmentedPointedObject F η X).obj.right ≫
      (coaugmentedPointedObject F η (pointedSSetSmashObject X Y)).obj.hom := by
  erw [← Category.assoc, coaugmentedPointed_axisLeft, ← F.map_comp]
  have h := congrArg Under.Hom.right (PointedObject.axisLeft_smashQuotient X.obj Y.obj)
  simp only [Under.comp_right, PointedObject.zero_right] at h
  erw [h]
  exact coaugmentedPointedConstant F η X (pointedSSetSmashObject X Y)

/-- 写した直積の第二軸も、同じ元の smash 商の像の下で零になる。 -/
lemma coaugmentedPointedSmash_axisRight (X Y : PointedSSetObject.{u}) :
    (PointedObject.axisRight (coaugmentedPointedObject F η X).obj
      (coaugmentedPointedObject F η Y).obj).right ≫
      μ F X.obj.right Y.obj.right ≫ F.map (PointedSimplicialSet.productToSmash X.obj Y.obj) =
    toUnit (coaugmentedPointedObject F η Y).obj.right ≫
      (coaugmentedPointedObject F η (pointedSSetSmashObject X Y)).obj.hom := by
  erw [← Category.assoc, coaugmentedPointed_axisRight, ← F.map_comp]
  have h := congrArg Under.Hom.right (PointedObject.axisRight_smashQuotient X.obj Y.obj)
  simp only [Under.comp_right, PointedObject.zero_right] at h
  erw [h]
  exact coaugmentedPointedConstant F η Y (pointedSSetSmashObject X Y)

/-- 元の乗法比較と smash 商の像は、両変数について reduced な実写像。 -/
def coaugmentedPointedSmashPair (X Y : PointedSSetObject.{u}) :
    PointedObject.ReducedPairMap (coaugmentedPointedObject F η X).obj
      (coaugmentedPointedObject F η Y).obj
      (coaugmentedPointedObject F η (pointedSSetSmashObject X Y)).obj :=
  ⟨μ F X.obj.right Y.obj.right ≫ F.map (PointedSimplicialSet.productToSmash X.obj Y.obj),
    (PointedObject.reduced_left_iff _).mpr (coaugmentedPointedSmash_axisRight F η X Y),
    (PointedObject.reduced_right_iff _).mpr (coaugmentedPointedSmash_axisLeft F η X Y)⟩

/-- 同じ元の smash の普遍性による、写した二つの値の smash からの前向き比較。 -/
def coaugmentedPointedSmashMap (X Y : PointedSSetObject.{u}) :
    (coaugmentedPointedObject F η X).obj ⊗ (coaugmentedPointedObject F η Y).obj ⟶
      (coaugmentedPointedObject F η (pointedSSetSmashObject X Y)).obj :=
  PointedObject.reducedToSmash (coaugmentedPointedSmashPair F η X Y)

/-- 元の直積からの商射上では、元の乗法比較と元の smash 商の像を厳密に回収する。 -/
lemma coaugmentedPointedSmashMap_quotient (X Y : PointedSSetObject.{u}) :
    PointedSimplicialSet.productToSmash (coaugmentedPointedObject F η X).obj
      (coaugmentedPointedObject F η Y).obj ≫ (coaugmentedPointedSmashMap F η X Y).right =
    μ F X.obj.right Y.obj.right ≫ F.map (PointedSimplicialSet.productToSmash X.obj Y.obj) :=
  congrArg Under.Hom.right (PointedObject.smashQuotient_desc
    (PointedObject.reducedPairPointed (coaugmentedPointedSmashPair F η X Y))
    (PointedObject.reducedPairPointed_axisLeft (coaugmentedPointedSmashPair F η X Y))
    (PointedObject.reducedPairPointed_axisRight (coaugmentedPointedSmashPair F η X Y)))

end SerrePositivity.KST.SConstruction
