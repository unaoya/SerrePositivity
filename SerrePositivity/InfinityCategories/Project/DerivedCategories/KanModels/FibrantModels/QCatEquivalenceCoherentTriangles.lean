module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.QCatEquivalenceCoherentHomInv
/-!
概要：指定 invHomIso と coherent な反対側の比較の両三角式を照合する。
方針：指定された同型の値と関手 ∞ 圏の二胞体を保持する。
規約：古い比較との一致を先取りしない。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma QCatEquivalence.coherentHomInvIso_left_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    Bicategory.leftZigzagIso (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.coherentHomInvIso.symm)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.invHomIso) =
      Bicategory.leftUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom) ≪≫
        (Bicategory.rightUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom)).symm := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.coherentHomInvIso_unit,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.adjointEquivalencePreservingCounit_counit]
  exact e.adjointEquivalencePreservingCounit.left_triangle

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_left_triangle)

lemma QCatEquivalence.coherentHomInvIso_right_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    Bicategory.rightZigzagIso (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.coherentHomInvIso.symm)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.invHomIso) =
      Bicategory.rightUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv) ≪≫
        (Bicategory.leftUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv)).symm := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.coherentHomInvIso_unit,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.adjointEquivalencePreservingCounit_counit]
  exact e.adjointEquivalencePreservingCounit.right_triangle

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_right_triangle)

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
