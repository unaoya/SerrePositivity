module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：固定の環写像による pushout を、filtered な係数図式とその余極限へ適用する。
方針：Under の lift と pushout の左随伴性、forget の filtered 余極限保存を使う。
規約：各段の両挿入との可換式と実際の cocone の普遍性を保持する。
使われ方：B03・B04 の被覆模型の係数段の移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {A B : CommRingCat.{u}} (F : J ⥤ CommRingCat.{u})
  (α : (Functor.const J).obj A ⟶ F) (f : A ⟶ B)
attribute [local instance] IsFiltered.nonempty

/-- 各係数段の実際の環の pushout からなる図式。 -/
def filteredPushoutRingDiagram : J ⥤ CommRingCat.{u} :=
  Under.lift F α ⋙ Under.pushout f ⋙ Under.forget B

/-- 係数図式の cocone に沿う、元の pushout への実際の cocone。 -/
def filteredPushoutRingCocone (c : Cocone F) (β : A ⟶ c.pt)
    (hβ : ∀ j, α.app j ≫ c.ι.app j = β) :
    Cocone (filteredPushoutRingDiagram F α f) :=
  (Under.pushout f ⋙ Under.forget B).mapCocone (Under.liftCocone F α c β hβ)

/-- 各段の pushout の cocone は、実際の filtered colimit。 -/
def filteredPushoutRingCoconeIsColimit (c : Cocone F) (β : A ⟶ c.pt)
    (hβ : ∀ j, α.app j ≫ c.ι.app j = β) (hc : IsColimit c) :
    IsColimit (filteredPushoutRingCocone F α f c β hβ) :=
  isColimitOfPreserves (Under.pushout f ⋙ Under.forget B)
    (Under.isColimitLiftCocone F α c β hβ hc)

/-- 各係数段から pushout への挿入は、実際の自然変換。 -/
def filteredPushoutRingInl : F ⟶ filteredPushoutRingDiagram F α f where
  app j := pushout.inl (α.app j) f
  naturality {j m} a := by
    dsimp [filteredPushoutRingDiagram, Under.lift, Under.pushout]
    simp

/-- cocone の射は pushout の第一挿入と可換。 -/
theorem filteredPushoutRingCocone_inl (c : Cocone F) (β : A ⟶ c.pt)
    (hβ : ∀ j, α.app j ≫ c.ι.app j = β) (j : J) :
    pushout.inl (α.app j) f ≫ (filteredPushoutRingCocone F α f c β hβ).ι.app j =
      c.ι.app j ≫ pushout.inl β f := by
  dsimp [filteredPushoutRingCocone, Under.liftCocone, Under.pushout]
  exact pushout.inl_desc _ _ _

/-- cocone の射は固定された環側の挿入と可換。 -/
theorem filteredPushoutRingCocone_inr (c : Cocone F) (β : A ⟶ c.pt)
    (hβ : ∀ j, α.app j ≫ c.ι.app j = β) (j : J) :
    pushout.inr (α.app j) f ≫ (filteredPushoutRingCocone F α f c β hβ).ι.app j =
      pushout.inr β f := by
  dsimp [filteredPushoutRingCocone, Under.liftCocone, Under.pushout]
  exact pushout.inr_desc _ _ _

end SerrePositivity.AlgebraicGeometry
