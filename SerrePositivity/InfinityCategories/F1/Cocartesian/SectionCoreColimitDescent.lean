module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionCoreColimitLift

/-!
概要：core の section の余極限への貼り合わせは各項を厳密に回収し、一意。
方針：core の包含と元の section の貼り合わせの普遍性で検証する。
規約：可逆変換の全高次を保持した、任意のパラメーターでの厳密な降下。
使われ方：境界・セル・骨格の core の比較を全体へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] [Small.{u} J]
  {T E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
  {D : J ⥤ Over B} (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))
  (s : ∀ j, T ⟶ (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p (D.obj j).hom) : SSet.{u}))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (D.map f)))

/-- core の貼り合わせの包含後は、元の section の族の貼り合わせそのもの。 -/
lemma cocartesianSectionCoreFamilyColimitLift_ι :
    cocartesianSectionCoreFamilyColimitLift p c hc s hs ≫
      (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p c.pt.hom)).ι =
    cocartesianSectionFamilyColimitLift p c hc
      (fun j ↦ s j ≫ (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p (D.obj j).hom)).ι)
      (cocartesianSectionCoreFamily_underlying_compatible p D s hs) :=
  cocartesianSectionCoreLift_of_vertex_cover_ι _ _ _ _ _ _ _ _

/-- 貼った core の族は、各項上の元の core の族を厳密に回収する。 -/
lemma cocartesianSectionCoreFamilyColimitLift_fac (j : J) :
    cocartesianSectionCoreFamilyColimitLift p c hc s hs ≫
      quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (c.ι.app j)) = s j :=
  cocartesianSectionCoreLift_of_vertex_cover_fac _ _ _ _ _ _ _ _ j

/-- 各項で指定した同じ core の族を回収する全体上の族は一意。 -/
lemma cocartesianSectionCoreFamilyColimitLift_unique
    (m : T ⟶ (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p c.pt.hom) : SSet.{u}))
    (hm : ∀ j, m ≫ quasicategoryCoreMap (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (c.ι.app j)) = s j) :
    m = cocartesianSectionCoreFamilyColimitLift p c hc s hs := by
  apply (cancel_mono (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p c.pt.hom)).ι).mp
  rw [cocartesianSectionCoreFamilyColimitLift_ι]
  apply cocartesianSectionFamilyColimitLift_unique
  intro j
  have h := congrArg (fun k ↦ k ≫
    (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p (D.obj j).hom)).ι) (hm j)
  rwa [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc] at h

end SerrePositivity.InfinityCategories
