module

public import Mathlib.CategoryTheory.Elements

/-!
概要：集合値の係数をULiftした要素圏と、元の要素圏の指定同値。
方針：要素だけをup・downし、基底の対象と射をそのまま保持する。
使われ方：HTT 4.2.4.4、RR02(a)の自由評価の小さいHom添字の宇宙移送。
規約：任意の小さい模型を選ばず、射影との一致を指定する。
-/

@[expose] public noncomputable section
universe t u v w
open CategoryTheory
namespace SerrePositivity.DiagramModel.ElementsUniverseLift
variable {K : Type w} [Category.{v} K] (F : K ⥤ Type u)

/-- 持ち上げた要素から、元の要素へ戻す指定関手。 -/
def down : (F ⋙ uliftFunctor.{t, u}).Elements ⥤ F.Elements where
  obj e := F.elementsMk e.obj e.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)

/-- 元の要素を標準的に持ち上げる指定関手。 -/
def up : F.Elements ⥤ (F ⋙ uliftFunctor.{t, u}).Elements where
  obj e := (F ⋙ uliftFunctor.{t, u}).elementsMk e.obj (ULift.up e.val)
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)

/-- up・downは対象・射を保って互いに逆になる。 -/
def equivalence : F.Elements ≌ (F ⋙ uliftFunctor.{t, u}).Elements where
  functor := up F
  inverse := down F
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply Functor.Elements.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply Functor.Elements.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)

  functor_unitIso_comp e := by
    apply Functor.Elements.Hom.ext
    change 𝟙 e.obj ≫ 𝟙 _ = 𝟙 _
    simp

/-- downは元の基底への射影を保つ。 -/
def downProjectionIso :
    down.{t} F ⋙ Functor.Elements.π F ≅ Functor.Elements.π (F ⋙ uliftFunctor.{t, u}) :=
  Iso.refl _

/-- upも同じ基底への射影を保つ。 -/
def upProjectionIso :
    up.{t} F ⋙ Functor.Elements.π (F ⋙ uliftFunctor.{t, u}) ≅ Functor.Elements.π F :=
  Iso.refl _

end SerrePositivity.DiagramModel.ElementsUniverseLift
