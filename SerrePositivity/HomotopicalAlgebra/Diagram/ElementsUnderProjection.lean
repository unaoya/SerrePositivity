module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：要素圏の始点を固定した射は、基底圏の始点を固定した射と同じ。
方針：終点の要素を関手の像で定め、射の一意な持ち上げを明示する。
使われ方：HTT 4.2.4.4、RR02(a)の自由評価の要素圏とBK重みの照合。
規約：指定射影によるUnder関手が同値であることを示す。
-/

@[expose] public noncomputable section
universe w v u
open CategoryTheory
namespace SerrePositivity.DiagramModel.ElementsUnderProjection
variable {K : Type u} [Category.{v} K] (F : K ⥤ Type w) (e : F.Elements)

/-- 始点の要素を押し出して得る、基底の射の指定持ち上げ。 -/
def liftObj (t : Under e.obj) : Under e :=
  Under.mk (show e ⟶ F.elementsMk t.right (F.map t.hom e.val) from
    { hom := t.hom, map_val := rfl })

/-- 基底の三角形も同じ射で一意に持ち上がる。 -/
def lift : Under e.obj ⥤ Under e where
  obj := liftObj F e
  map {t s} f := Under.homMk
    (show (liftObj F e t).right ⟶ (liftObj F e s).right from
      { hom := f.right
        map_val := by
          change F.map f.right (F.map t.hom e.val) = F.map s.hom e.val
          rw [← FunctorToTypes.map_comp_apply, Under.w f] })
    (by apply Functor.Elements.Hom.ext; exact Under.w f)
  map_id _ := by apply Under.UnderMorphism.ext; apply Functor.Elements.Hom.ext; rfl
  map_comp _ _ := by apply Under.UnderMorphism.ext; apply Functor.Elements.Hom.ext; rfl

/-- 射影して持ち上げ直した終点は、射の要素条件によって元の終点に一致する。 -/
def unitComponent (t : Under e) :
    t ≅ (lift F e).obj ((Under.post (Functor.Elements.π F)).obj t) :=
  Under.isoMk (Functor.Elements.isoMk (Iso.refl t.right.obj) (by
    change F.map (𝟙 t.right.obj) t.right.val = F.map t.hom.hom e.val
    simpa using t.hom.map_val.symm)) (by
      apply Functor.Elements.Hom.ext
      change t.hom.hom ≫ 𝟙 _ = t.hom.hom
      exact Category.comp_id _)

/-- 指定射影に沿うUnder圏の同値。 -/
def equivalence : Under e ≌ Under e.obj where
  functor := Under.post (Functor.Elements.π F)
  inverse := lift F e
  unitIso := NatIso.ofComponents (unitComponent F e) (by
    intro t s f
    apply Under.UnderMorphism.ext
    apply Functor.Elements.Hom.ext
    change f.right.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.right.hom
    simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro t s f
    apply Under.UnderMorphism.ext
    change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right
    simp)
  functor_unitIso_comp t := by
    apply Under.UnderMorphism.ext
    change 𝟙 t.right.obj ≫ 𝟙 _ = 𝟙 _
    simp

end SerrePositivity.DiagramModel.ElementsUnderProjection
