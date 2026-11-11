module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction
/-!
概要：実 ∞ 圏同値の指定 invHomIso を保ったまま三角式付き同値を構成する。
方針：逆方向の同値を adjointify し、逆同型と右三角式で向きを戻す。
規約：元の homInvIso との一致は主張しない。使われ方：cell 比較の単位整合性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
def QCatEquivalence.adjointEquivalencePreservingCounit {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    Bicategory.Equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv
  unit := e.symm.adjointEquivalence.counit.symm
  counit := e.symm.adjointEquivalence.unit.symm
  left_triangle := by
    have h := congrArg Iso.symm e.symm.adjointEquivalence.right_triangle
    simpa only [Bicategory.rightZigzagIso_symm, Iso.trans_symm, Iso.symm_symm_eq] using! h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (adjointEquivalencePreservingCounit)

lemma QCatEquivalence.adjointEquivalencePreservingCounit_counit {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.adjointEquivalencePreservingCounit.counit = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.invHomIso := by
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.invHomIso.symm).symm = _
  apply Iso.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (adjointEquivalencePreservingCounit_counit)

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
