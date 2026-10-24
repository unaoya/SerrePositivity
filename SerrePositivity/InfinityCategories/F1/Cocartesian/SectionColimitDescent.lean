module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionColimitLift

/-!
概要：余極限上へ貼った section の族の制限公式と一意性。
方針：uncurry の単射性で、パラメーターとの直積の余極限の普遍性へ戻す。
規約：元の各項の族と高次のパラメーターを厳密に保持する。
使われ方：section の core の族の余極限に沿う厳密な降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] [Small.{u} J]
  {T E B : SSet.{u}} (p : E ⟶ B) {D : J ⥤ Over B} (c : Cocone D)
  (hc : IsColimit ((Over.forget B).mapCocone c))
  (s : ∀ j, T ⟶ SerrePositivity.InfinityCategories.cocartesianSections p (D.obj j).hom)
  (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ SerrePositivity.InfinityCategories.cocartesianSectionsPre p (D.map f))

/-- 貼った section の族の展開は、元の直積上の貼り合わせの図式。 -/
lemma cocartesianSectionFamilyColimitLift_uncurry :
    SerrePositivity.InfinityCategories.cocartesianSectionsUncurry (cocartesianSectionFamilyColimitLift p c hc s hs) =
      cocartesianSectionFamilyColimitUncurry p c hc s hs :=
  SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_curry _ _ _

/-- 貼った section の族は、各項上の指定された元の族を厳密に回収する。 -/
lemma cocartesianSectionFamilyColimitLift_fac (j : J) :
    cocartesianSectionFamilyColimitLift p c hc s hs ≫
      SerrePositivity.InfinityCategories.cocartesianSectionsPre p (c.ι.app j) = s j := by
  apply SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_injective p (D.obj j).hom
  rw [SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_overPre,
    cocartesianSectionFamilyColimitLift_uncurry, cocartesianSectionFamilyColimitUncurry_fac]

/-- 同じ各項の族を厳密に回収する section の族は一意。 -/
lemma cocartesianSectionFamilyColimitLift_unique (m : T ⟶ SerrePositivity.InfinityCategories.cocartesianSections p c.pt.hom)
    (hm : ∀ j, m ≫ SerrePositivity.InfinityCategories.cocartesianSectionsPre p (c.ι.app j) = s j) :
    m = cocartesianSectionFamilyColimitLift p c hc s hs := by
  apply SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_injective p c.pt.hom
  rw [cocartesianSectionFamilyColimitLift_uncurry]
  apply (cocartesianSectionTensorCocone_isColimit c hc).hom_ext
  intro j
  change ((c.ι.app j).left ▷ T) ≫ SerrePositivity.InfinityCategories.cocartesianSectionsUncurry m =
    ((c.ι.app j).left ▷ T) ≫ cocartesianSectionFamilyColimitUncurry p c hc s hs
  rw [← SerrePositivity.InfinityCategories.cocartesianSectionsUncurry_overPre, hm j,
    cocartesianSectionFamilyColimitUncurry_fac]

end SerrePositivity.InfinityCategories
