module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalencePreservingCounit
/-!
概要：指定 invHomIso を保つ三角式付き同値から反対側の比較を回収する。
方針：指定済みの実射と比較同型の値を保持して照合する。
規約：生の dg 射の関手性や古い homInvIso の三角式は先取りしない。
使われ方：一般 cell 合成の五角式・単位三角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def QCatEquivalence.coherentHomInvIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ e.inv) (𝟙 X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).mapIso e.adjointEquivalencePreservingCounit.unit.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso)

lemma QCatEquivalence.coherentHomInvIso_unit {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.coherentHomInvIso.symm =
      e.adjointEquivalencePreservingCounit.unit := by
  apply Iso.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).map_injective
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv)).symm _) = _
  exact Equiv.apply_symm_apply _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_unit)

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
