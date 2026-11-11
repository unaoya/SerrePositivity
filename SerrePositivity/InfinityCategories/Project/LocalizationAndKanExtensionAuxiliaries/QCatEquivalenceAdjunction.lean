module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
/-!
概要：実 ∞ 圏同値の両比較同型を、三角恒等式を満たす実 ∞ 随伴へ昇格する。
方針：h Fun の同型を双圏の二同型へ戻し、余単位を adjointify する。
規約：hC と hD の随伴ではなく、関手 ∞ 圏の二胞体を使う。
使われ方：β5 の Morita tensor の右随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open CategoryTheory SSet
/-- 同じ実関手間の全関手同型を、quasicategory 双圏の二同型へ戻す。 -/
def functorIsoToQcatIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F G : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G where
  hom := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv F G).symm e.hom
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv G F).symm e.inv
  hom_inv_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map_injective
    exact e.inv_hom_id
/-- 実 ∞ 圏同値の前向き写像と同じ逆写像による、三角式付きの双圏同値。 -/
def QCatEquivalence.adjointEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    Bicategory.Equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv)
    (functorIsoToQcatIso e.homInvIso.symm) (functorIsoToQcatIso e.invHomIso)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalence (adjointEquivalence)

/-- 実 ∞ 圏同値には、指定の逆関手を右随伴とする実 ∞ 随伴がある。 -/
def QCatEquivalence.toAdjunction {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction e.hom e.inv := e.adjointEquivalence.adj

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalence (toAdjunction)

/-- 同値を横辺とする全関手比較四角形を、同じ逆関手の四角形へ移す。 -/
def QCatEquivalence.inverseSquareIso {A B C D : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D)
    (a : C ⟶ A) (b : D ⟶ B) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ e.hom) (p.hom ≫ b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ e.inv) (p.inv ≫ a) := by
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp p.invHomIso.symm (b ≫ e.inv)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp h.symm p.inv) e.inv
  have h₂ := e.homInvIso.precomp (p.inv ≫ a)
  have q₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ e.inv) (p.inv ≫ p.hom ≫ b ≫ e.inv) := by
    simpa only [Category.assoc, Category.id_comp] using h₀
  have q₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p.inv ≫ p.hom ≫ b ≫ e.inv)
      (p.inv ≫ a ≫ e.hom ≫ e.inv) := by
    simpa only [Category.assoc] using h₁
  have q₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p.inv ≫ a ≫ e.hom ≫ e.inv) (p.inv ≫ a) := by
    simpa only [Category.assoc, Category.comp_id] using h₂
  exact q₀.trans (q₁.trans q₂)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalence (inverseSquareIso)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
