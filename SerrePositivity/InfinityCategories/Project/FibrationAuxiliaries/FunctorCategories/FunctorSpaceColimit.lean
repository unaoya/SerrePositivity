module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：底の余極限を覆う関手の族を、全パラメーターで一意に貼り合わせる。
方針：族を展開し、右直積による余極限の保存を使う。
規約：標的の充填性を仮定せず、元の制限を厳密に回収する。
使われ方：分類先の区間 Hom の底に関する降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

variable {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{u}} {T X : SSet.{u}}
  (c : Cocone D) (hc : IsColimit c)
  (s : ∀ j, T ⟶ (ihom (D.obj j)).obj X)
  (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ (pre (D.map f)).app X)

/-- 関手の族の展開は、同じパラメーターを持つ余錐となる。 -/
def functorSpaceFamilyTensorCocone : Cocone (D ⋙ tensorRight T) where
  pt := X
  ι :=
    { app j := uncurry (s j)
      naturality {j k} f := by
        change (D.map f ▷ T) ≫ uncurry (s k) = uncurry (s j)
        rw [hs f, uncurry_pre_app] }

/-- 底の余極限上へ元の関手の族を貼り合わせる。 -/
def functorSpaceColimitLift : T ⟶ (ihom c.pt).obj X :=
  curry ((isColimitOfPreserves (tensorRight T) hc).desc
    (functorSpaceFamilyTensorCocone s hs))

/-- 貼り合わせた族は、各項上の元の族を同じ制限で回収する。 -/
lemma functorSpaceColimitLift_fac (j : J) :
    functorSpaceColimitLift c hc s hs ≫ (pre (c.ι.app j)).app X = s j := by
  apply uncurry_injective
  rw [uncurry_pre_app, functorSpaceColimitLift, uncurry_curry]
  exact (isColimitOfPreserves (tensorRight T) hc).fac
    (functorSpaceFamilyTensorCocone s hs) j

include hc in
/-- 余極限の各項への制限は、全体上の同じ関手の族を一意に決める。 -/
lemma functorSpaceColimit_hom_ext (a b : T ⟶ (ihom c.pt).obj X)
    (h : ∀ j, a ≫ (pre (c.ι.app j)).app X = b ≫ (pre (c.ι.app j)).app X) : a = b := by
  apply uncurry_injective
  apply (isColimitOfPreserves (tensorRight T) hc).hom_ext
  intro j
  change (c.ι.app j ▷ T) ≫ uncurry a = (c.ι.app j ▷ T) ≫ uncurry b
  simpa only [uncurry_pre_app] using congrArg uncurry (h j)

/-- 元の各制限を持つ族は、構成した同じ貼り合わせに等しい。 -/
lemma functorSpaceColimitLift_unique (m : T ⟶ (ihom c.pt).obj X)
    (hm : ∀ j, m ≫ (pre (c.ι.app j)).app X = s j) :
    m = functorSpaceColimitLift c hc s hs := by
  apply functorSpaceColimit_hom_ext c hc
  intro j
  rw [hm j, functorSpaceColimitLift_fac]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
