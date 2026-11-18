module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsUniverseLift
public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：同じ集合値前層の要素圏を、siteと値の指定された宇宙持ち上げに沿って移す。
方針：AsSmallのup/downとULiftのup/downを同時に適用し、射影と前層の射を保つ。
規約：HTT 5.1.5.6、6.2.2.6の重み付き切断に使う既存構成の係数移送の法則。
  Kerodon §7.1（Tag 02H1）。小さい通常のsiteのČech層の模型に限る。
使われ方：S8の任意の係数を表現可能な空間値で検出するとき、元の要素を指定して運ぶ。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- siteと値を同時に一段持ち上げた、元の同じ集合値前層。 -/
def siteLiftPresheaf (P : Cᵒᵖ ⥤ Type u) : (AsSmall.{u + 1} C)ᵒᵖ ⥤ Type (u + 1) :=
  (AsSmall.down : AsSmall.{u + 1} C ⥤ C).op ⋙ P ⋙ uliftFunctor.{u + 1, u}

/-- 持ち上げた要素から元の要素へ戻す、同じ射影を保つ関手。 -/
def siteLiftElementsDown (P : Cᵒᵖ ⥤ Type u) :
    (siteLiftPresheaf P).Elements ⥤ P.Elements where
  obj e := P.elementsMk ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).op.obj e.obj) e.val.down
  map f := Functor.Elements.homMk
    ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).op.map f.hom)
    (congrArg ULift.down f.map_val)

/-- 元の要素を、siteと値の同じ指定upで持ち上げる関手。 -/
def siteLiftElementsUp (P : Cᵒᵖ ⥤ Type u) :
    P.Elements ⥤ (siteLiftPresheaf P).Elements where
  obj e := (siteLiftPresheaf P).elementsMk
    ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).op.obj e.obj) (ULift.up e.val)
  map f := Functor.Elements.homMk
    ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).op.map f.hom)
    (congrArg ULift.up f.map_val)

/-- 指定up/downは元の要素を保って互いに逆となる。 -/
def siteLiftElementsEquivalence (P : Cᵒᵖ ⥤ Type u) :
    P.Elements ≌ (siteLiftPresheaf P).Elements where
  functor := siteLiftElementsUp P
  inverse := siteLiftElementsDown P
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
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- 元の前層の射を、指定したsiteと値の移送に沿って運ぶ。 -/
def siteLiftPresheafMap {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    siteLiftPresheaf P ⟶ siteLiftPresheaf Q :=
  Functor.whiskerRight (Functor.whiskerLeft (AsSmall.down : AsSmall.{u + 1} C ⥤ C).op φ)
    uliftFunctor.{u + 1, u}

/-- downは同じ前層の射に自然であり、要素圏の射を選び直さない。 -/
lemma siteLiftElementsDown_naturality {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    (siteLiftPresheafMap φ).mapElements ⋙ siteLiftElementsDown Q =
      siteLiftElementsDown P ⋙ φ.mapElements := rfl

/-- 指定downは元のsiteへの射影を厳密に保つ。 -/
lemma siteLiftElementsDown_projection (P : Cᵒᵖ ⥤ Type u) :
    siteLiftElementsDown P ⋙ Functor.Elements.π P =
      Functor.Elements.π (siteLiftPresheaf P) ⋙
        (AsSmall.down : AsSmall.{u + 1} C ⥤ C).op := rfl

end SerrePositivity.InfinityCategories.Sheaves
