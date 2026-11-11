module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence

/-!
概要：底上の同値によって相対写像空間の始域と標的を同時に置き換える。
方針：標的側の後合成の同値と、始域側の前合成の同値の逆を合成する。
規約：始域側の底上の対象には left fibration 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の復元比較による写像空間の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底を保つ前合成同値で始域と標的を比較すると、相対写像空間は同値になる。
方針：標的側の後合成で写した後、始域側の前合成の同値を逆向きに使う。
規約：p と q の射影は left fibration、底 B は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、二つの復元比較による相対写像空間の置き換え。 -/
noncomputable def relativeFunctorEquivalenceOfComparisons
    {B : SSet.{u}} [Quasicategory B] (a b p q : Over B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom]
    (f : a ⟶ b) (g : p ⟶ q)
    (ef : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.left) (eg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.hom b.hom) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p.hom q.hom g.left g.w eg a.hom).choose.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence q.hom f ef).choose.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
