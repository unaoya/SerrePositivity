module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
概要：μ-small な形状は、通常の単体集合圏の μ-presentable 対象となる。
方針：元の単体圏による表現可能対象の密度表示と、μ-small な余極限閉性を使う。
規約：これは strict な SSet の表示性。Space 内の μ-compact 性とは区別する。
使われ方：μ-filtered な通常の余極限への全単体での因子化。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite SSet CategoryTheory.Presheaf
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 非可算正則 μ に対して、元の μ-small な単体集合は通常の意味で μ-presentable。 -/
lemma smallShape_isCardinalPresentable {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : SSet.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) :
    IsCardinalPresentable K μ := by
  have hA : HasCardinalLT (Arrow K.Elementsᵒᵖ) μ := by
    simpa only [hasCardinalLT_arrow_op_iff] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasCardinalLT_simplexCategory_arrow hμ hK
  have (k : K.Elementsᵒᵖ) : IsCardinalPresentable ((functorToRepresentables K).obj k) μ := by
    dsimp only [functorToRepresentables, Functor.comp_obj]
    infer_instance
  exact isCardinalPresentable_of_isColimit' (coconeOfRepresentable K)
    (colimitOfRepresentable K) μ hA

/-- 元の μ-small な形状からの射は、指定された μ-filtered strict 余極限の一段を通る。 -/
lemma smallShape_factorization {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {I : Type u} [SmallCategory I] [IsCardinalFiltered I μ]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c) (f : K ⟶ c.pt) :
    ∃ (i : I) (g : K ⟶ F.obj i), g ≫ c.ι.app i = f := by
  have := smallShape_isCardinalPresentable hμ K hK
  exact IsCardinalPresentable.exists_hom_of_isColimit μ hc f

/-- 元の二つの図式写像の等式は、同じ μ-filtered strict 余極限の共通の後続段で成立する。 -/
lemma smallShape_eventual_equality {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {I : Type u} [SmallCategory I] [IsCardinalFiltered I μ]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    {i j : I} (f : K ⟶ F.obj i) (g : K ⟶ F.obj j)
    (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k), f ≫ F.map a = g ≫ F.map b := by
  have := smallShape_isCardinalPresentable hμ K hK
  exact IsCardinalPresentable.exists_eq_of_isColimit μ hc f g h

/-- 元の μ-small な境界の値を保ち、同じ全図式を一つの後続段へ因子化する。 -/
lemma smallShape_relative_factorization {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {A B : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ B) (i : A ⟶ B)
    {I : Type u} [SmallCategory I] [IsCardinalFiltered I μ]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (j : I) (a : A ⟶ F.obj j) (b : B ⟶ c.pt) (h : a ≫ c.ι.app j = i ≫ b) :
    ∃ (k : I) (v : j ⟶ k) (g : B ⟶ F.obj k),
      i ≫ g = a ≫ F.map v ∧ g ≫ c.ι.app k = b := by
  obtain ⟨l, g, hg⟩ := smallShape_factorization hμ hB hc b
  obtain ⟨k, v, w, hw⟩ := smallShape_eventual_equality hμ hA hc a (i ≫ g) (by
    rw [Category.assoc, hg]
    exact h)
  refine ⟨k, v, g ≫ F.map w, ?_, ?_⟩
  · exact (Category.assoc i g (F.map w)).symm.trans hw.symm
  · rw [Category.assoc, c.w w, hg]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
