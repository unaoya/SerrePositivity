module

public import SerrePositivity.AlgebraicGeometry.FilteredPushoutRingModel
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
概要：filtered pushout の cocone の頂点を、指定した実際の pushout 模型に保つ。
方針：IsPushout の canonical な同型で cocone と普遍性を移送する。
規約：係数環側と固定した環側の両挿入との可換式を保持する。
使われ方：B03・B04 の元の tensor 模型への係数段の写像の因子化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {A B : CommRingCat.{u}} (F : J ⥤ CommRingCat.{u})
  (α : (Functor.const J).obj A ⟶ F) (f : A ⟶ B)
  (c : Cocone F) (β : A ⟶ c.pt) (hβ : ∀ j, α.app j ≫ c.ι.app j = β)
  {P : CommRingCat.{u}} (i : c.pt ⟶ P) (j : B ⟶ P) (H : IsPushout β f i j)

/-- 指定した実際の pushout を頂点とする、各係数段の pushout の cocone。 -/
def filteredPushoutRingPointCocone : Cocone (filteredPushoutRingDiagram F α f) :=
  (filteredPushoutRingCocone F α f c β hβ).extend H.isoPushout.inv

/-- 指定した実際の pushout は、係数段ごとの pushout の filtered colimit。 -/
def filteredPushoutRingPointCoconeIsColimit (hc : IsColimit c) :
    IsColimit (filteredPushoutRingPointCocone F α f c β hβ i j H) :=
  IsColimit.extendIso (s := filteredPushoutRingCocone F α f c β hβ) H.isoPushout.inv
    (filteredPushoutRingCoconeIsColimit F α f c β hβ hc)

/-- 元の係数 cocone と指定した第一挿入は、各段の第一挿入と可換。 -/
theorem filteredPushoutRingPointCocone_inl (a : J) :
    pushout.inl (α.app a) f ≫
      (filteredPushoutRingPointCocone F α f c β hβ i j H).ι.app a = c.ι.app a ≫ i := by
  change pushout.inl (α.app a) f ≫
    (filteredPushoutRingCocone F α f c β hβ).ι.app a ≫ H.isoPushout.inv = _
  rw [← Category.assoc, filteredPushoutRingCocone_inl, Category.assoc, H.inl_isoPushout_inv]

/-- 指定した第二挿入は、全ての係数段で同じ可換式を満たす。 -/
theorem filteredPushoutRingPointCocone_inr (a : J) :
    pushout.inr (α.app a) f ≫
      (filteredPushoutRingPointCocone F α f c β hβ i j H).ι.app a = j := by
  change pushout.inr (α.app a) f ≫
    (filteredPushoutRingCocone F α f c β hβ).ι.app a ≫ H.isoPushout.inv = _
  rw [← Category.assoc, filteredPushoutRingCocone_inr, H.inr_isoPushout_inv]

end SerrePositivity.AlgebraicGeometry
