module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedMaps
public import SerrePositivity.Spectra.Pointed.ReducedPair

/-! # 有限積保存と monoidal 単位が保つ基点・零写像
概要：写した基点と定数写像を元の monoidal 単位で回収し、直積の両軸と比較する。
方針：単位の自然性、終対象比較、有限積の乗法比較を使う。
規約：一般の monoidal な基礎関手について証明する。使われ方：Ex∞ の smash 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の基点の単位への像は、monoidal 単位から写した元の基点と一致する。 -/
lemma coaugmentedPointedObject_basepoint (X : PointedSSetObject.{u}) :
    (coaugmentedPointedObject F η X).obj.hom = ε F ≫ F.map X.obj.hom := by
  have hn := η.naturality X.obj.hom
  have hu := NatTrans.IsMonoidal.unit (τ := η)
  change 𝟙 _ ≫ η.app (𝟙_ SSet.{u}) = ε F at hu
  change X.obj.hom ≫ η.app X.obj.right = _
  exact hn.trans (congrArg (fun e => e ≫ F.map X.obj.hom)
    ((Category.id_comp _).symm.trans hu))

/-- 元の基点への定数射は、写した対象の同じ基点への定数射に写る。 -/
lemma coaugmentedPointedConstant (X Y : PointedSSetObject.{u}) :
    F.map (toUnit X.obj.right ≫ Y.obj.hom) =
      toUnit (coaugmentedPointedObject F η X).obj.right ≫
        (coaugmentedPointedObject F η Y).obj.hom := by
  erw [F.map_comp, coaugmentedPointedObject_basepoint, ← Category.assoc,
    Functor.Monoidal.toUnit_ε]
  rfl

/-- 乗法比較は、写した直積の第一軸を元の第一軸の像へ送る。 -/
lemma coaugmentedPointed_axisLeft (X Y : PointedSSetObject.{u}) :
    (PointedObject.axisLeft (coaugmentedPointedObject F η X).obj
      (coaugmentedPointedObject F η Y).obj).right ≫ μ F X.obj.right Y.obj.right =
    F.map (PointedObject.axisLeft X.obj Y.obj).right := by
  simp only [PointedObject.axisLeft, PointedObject.prodLift,
    Under.id_right, PointedObject.zero_right]
  change lift (𝟙 (F.obj X.obj.right))
    (toUnit (F.obj X.obj.right) ≫ (coaugmentedPointedObject F η Y).obj.hom) ≫
      μ F X.obj.right Y.obj.right =
    F.map (lift (𝟙 X.obj.right) (toUnit X.obj.right ≫ Y.obj.hom))
  erw [← coaugmentedPointedConstant F η X Y, ← F.map_id X.obj.right,
    Functor.Monoidal.lift_μ]

/-- 乗法比較は、写した直積の第二軸を元の第二軸の像へ送る。 -/
lemma coaugmentedPointed_axisRight (X Y : PointedSSetObject.{u}) :
    (PointedObject.axisRight (coaugmentedPointedObject F η X).obj
      (coaugmentedPointedObject F η Y).obj).right ≫ μ F X.obj.right Y.obj.right =
    F.map (PointedObject.axisRight X.obj Y.obj).right := by
  simp only [PointedObject.axisRight, PointedObject.prodLift,
    Under.id_right, PointedObject.zero_right]
  change lift (toUnit (F.obj Y.obj.right) ≫
    (coaugmentedPointedObject F η X).obj.hom) (𝟙 (F.obj Y.obj.right)) ≫
      μ F X.obj.right Y.obj.right =
    F.map (lift (toUnit Y.obj.right ≫ X.obj.hom) (𝟙 Y.obj.right))
  erw [← coaugmentedPointedConstant F η Y X, ← F.map_id Y.obj.right,
    Functor.Monoidal.lift_μ]

end SerrePositivity.KST.SConstruction
