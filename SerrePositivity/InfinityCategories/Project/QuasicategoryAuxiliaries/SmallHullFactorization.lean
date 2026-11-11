module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallQuasicategoryHull

/-!
概要：任意の各次数で小さい大宇宙の形状も、同じ小模型へ厳密因子化する。
方針：源の Shrink 同型を一度通し、既存の全図式因子化を使ってから戻す。
規約：源の充填性は不要。因子化先と包含を変えない。
使われ方：Ind-S (4) の大宇宙の境界・円柱形状。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 小さい次数を持つ任意の大宇宙の形状の図式を、同じ包含へ厳密因子化する。 -/
lemma Hull.factor_small {X K : SSet.{max u v}} {A : X.Subcomplex}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Hull.{u, v} X A) [∀ d, Small.{u} (K.obj d)]
    (f : K ⟶ X) (hf : SSet.Subcomplex.range f ≤ A) :
    ∃ g : K ⟶ (SSet.uliftFunctor.{v, u}).obj H.obj, g ≫ H.inclusion = f := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.modelIso.{u, v} K
  have hr : SSet.Subcomplex.range (e.hom ≫ f) ≤ A := by
    intro d x hx
    obtain ⟨y, rfl⟩ := hx
    exact hf _ ⟨e.hom.app d y, rfl⟩
  obtain ⟨g, hg⟩ := H.factor (e.hom ≫ f) hr
  refine ⟨e.inv ≫ (SSet.uliftFunctor.{v, u}).map g, ?_⟩
  rw [Category.assoc, hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Hull export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Hull (factor_small)


end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
