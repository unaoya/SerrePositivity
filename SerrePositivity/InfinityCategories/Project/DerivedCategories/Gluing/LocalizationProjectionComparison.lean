module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.KST.SConstruction.FunctorIsoEquivalenceReflection
/-!
概要：同じ局所化に沿って反転し、指定切断上で恒等となる関手を元射影へ全比較する。
方針：実関手同型付き延長を取り、同じ切断で延長が恒等関手であることを全関手同型で回収する。
規約：対象別比較ではなく元の関手全体を比較する。使われ方：恒等 cone 差の同定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {B C : SSet.{u}} [Quasicategory B] [Quasicategory C]

def localizationProjectionComparison (q : B ⟶ C) (W : Set (B _⦋1⦌))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W) (s : C ⟶ B) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s ≫ q) (𝟙 C))
    (r : B ⟶ C) (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges r W) (hsr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s ≫ r) (𝟙 C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r q := by
  let g := (hq.exists_extension r hr).choose
  let h := (hq.exists_extension r hr).choose_spec.some
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (s ≫ q ≫ g) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hs.symm g
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s ≫ q ≫ g) (s ≫ r) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using h.precomp s
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (𝟙 C) := h₁.trans (h₂.trans hsr)
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (hg.precomp q) rfl (Category.comp_id q))

def localizationProjectionComparisonOfTest {T : SSet.{u}} [Quasicategory T]
    (q : B ⟶ C) (W : Set (B _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W)
    (j : T ⟶ B) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (j ≫ q))
    (r : B ⟶ C) (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges r W) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (j ≫ r) (j ≫ q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r q := by
  let g := (hq.exists_extension r hr).choose
  let h := (hq.exists_extension r hr).choose_spec.some
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((j ≫ q) ≫ g) ((j ≫ q) ≫ 𝟙 C) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((h.precomp j).trans ht) (Category.assoc _ _ _).symm
      (Category.comp_id _).symm
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (𝟙 C) := KST.SConstruction.functorIsoReflectPreEquivalence hj.choose h₁
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (hg.precomp q) rfl (Category.comp_id q))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
