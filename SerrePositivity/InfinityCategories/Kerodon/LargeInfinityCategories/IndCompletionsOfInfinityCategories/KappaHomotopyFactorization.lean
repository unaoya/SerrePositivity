module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.KappaRelativeFactorization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.KappaSmallProducts
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：κ-small な形状からの元のホモトピーは、通常の κ-filtered 余極限の後続段で両端を保って実現できる。
方針：κ-small な円柱と κ-presentable な二端点を、同じ後続段へ相対因子分解する。
規約：元の二つの射と元の段からの射を厳密に保持する。
使われ方：coherent な κ-filtered 比較に必要なホモトピーの段階検出。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ κ-small な形状からのホモトピーは、元の二端点を保つ同じ後続段で実現できる。 -/
lemma exists_homotopy_at_stage_of_kappaFiltered_isColimit
    {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {I : Type u} [SmallCategory I] [IsCardinalFiltered I κ]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (j : I) (f g : K ⟶ F.obj j)
    (H : SSet.Homotopy (f ≫ c.ι.app j) (g ≫ c.ι.app j)) :
    ∃ (k : I) (v : j ⟶ k), Nonempty (SSet.Homotopy (f ≫ F.map v) (g ≫ F.map v)) := by
  have hκ : κ.IsRegular := Fact.out
  have : IsCardinalPresentable K κ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isCardinalPresentable_of_isKappaSmall hK
  have (s : Discrete WalkingPair) : IsCardinalPresentable ((pair K K).obj s) κ := by
    rcases s with ⟨_ | _⟩ <;> dsimp <;> infer_instance
  have : IsCardinalPresentable (K ⨿ K) κ :=
    isCardinalPresentable_of_isColimit _ (coprodIsCoprod K K) κ
      (hasCardinalLT_of_finite _ _ hκ.aleph0_le)
  have : IsCardinalPresentable (K ⊗ (Δ[1] : SSet.{u})) κ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isCardinalPresentable_of_isKappaSmall
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_prod hκ hK (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _))
  let i : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) := coprod.desc SSet.ι₀ SSet.ι₁
  have hi : coprod.desc f g ≫ c.ι.app j = i ≫ H.h := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, coprod.inl_desc, H.h₀]
    · rw [← Category.assoc, coprod.inr_desc, ← Category.assoc, coprod.inr_desc, H.h₁]
  obtain ⟨l, h, hh⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc H.h
  obtain ⟨k, v, w, hw⟩ := IsCardinalPresentable.exists_eq_of_isColimit κ hc
    (coprod.desc f g) (i ≫ h) (by rw [Category.assoc, hh]; exact hi)
  refine ⟨k, v, ⟨{ h := h ≫ F.map w, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩⟩
  · change SSet.ι₀ ≫ (h ≫ F.map w) = f ≫ F.map v
    have he := congrArg (fun t => (coprod.inl : K ⟶ K ⨿ K) ≫ t) hw
    simpa only [i, ← Category.assoc, coprod.inl_desc] using he.symm
  · change SSet.ι₁ ≫ (h ≫ F.map w) = g ≫ F.map v
    have he := congrArg (fun t => (coprod.inr : K ⟶ K ⨿ K) ≫ t) hw
    simpa only [i, ← Category.assoc, coprod.inr_desc] using he.symm
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
