module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.KappaSmallPresentable

/-!
概要：κ-small な形状から通常の κ-filtered 余極限への射を、指定された境界を保つ一つの段へ下ろす。
方針：κ-presentability で射と境界上の等式を同じ後続段へ因子分解する。
規約：ここでは通常の小圏による strict 図式と実際の通常の余極限余錐を使う。
使われ方：一般の正則 κ における図式の相対因子分解の入力。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
variable {κ : Cardinal.{u}} [Fact κ.IsRegular]
  {I : Type u} [SmallCategory I] [IsCardinalFiltered I κ]
  {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
include hc

/-- 元の κ-small な形状から同じ余極限への射は、同じ図式の一つの段を通る。 -/
lemma kappaSmall_factorization_of_isColimit {A : SSet.{u}}
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (f : A ⟶ c.pt) :
    ∃ (i : I) (g : A ⟶ F.obj i), g ≫ c.ι.app i = f := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isCardinalPresentable_of_isKappaSmall hA
  exact IsCardinalPresentable.exists_hom_of_isColimit κ hc f

/-- κ-small な元の境界を指定した射は、元の段からの射と境界を保つ一つの後続段で実現できる。 -/
lemma kappaSmall_relative_factorization_of_isColimit {A B : SSet.{u}}
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B) (i : A ⟶ B)
    (j : I) (a : A ⟶ F.obj j) (b : B ⟶ c.pt) (h : a ≫ c.ι.app j = i ≫ b) :
    ∃ (k : I) (v : j ⟶ k) (g : B ⟶ F.obj k),
      i ≫ g = a ≫ F.map v ∧ g ≫ c.ι.app k = b := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isCardinalPresentable_of_isKappaSmall hA
  obtain ⟨l, g, hg⟩ := kappaSmall_factorization_of_isColimit hc hB b
  obtain ⟨k, v, w, hw⟩ := IsCardinalPresentable.exists_eq_of_isColimit κ hc a (i ≫ g) (by
    rw [Category.assoc, hg]
    exact h)
  refine ⟨k, v, g ≫ F.map w, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans hw.symm
  · rw [Category.assoc, c.w w]
    exact hg

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
