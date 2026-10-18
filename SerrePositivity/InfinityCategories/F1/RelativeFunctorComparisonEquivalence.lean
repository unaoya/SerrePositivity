module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPostEquivalence

/-!
概要：底上の同値によって相対写像空間の始域と標的を同時に置き換える。
方針：標的側の後合成の同値と、始域側の前合成の同値の逆を合成する。
規約：始域側の底上の対象には left fibration 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening の復元比較による写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底を保つ前合成同値で始域と標的を比較すると、相対写像空間は同値になる。
方針：標的側の後合成で写した後、始域側の前合成の同値を逆向きに使う。
規約：p と q の射影は left fibration、底 B は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6、二つの復元比較による相対写像空間の置き換え。 -/
noncomputable def relativeFunctorEquivalenceOfComparisons
    {B : SSet.{u}} [Quasicategory B] (a b p q : Over B)
    [LeftFibration p.hom] [LeftFibration q.hom]
    (f : a ⟶ b) (g : p ⟶ q)
    (ef : IsPrecompositionEquivalence f.left) (eg : IsPrecompositionEquivalence g.left) :
    QCatEquivalence (relativeFunctorSpace p.hom a.hom) (relativeFunctorSpace q.hom b.hom) :=
  (relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p.hom q.hom g.left g.w eg a.hom).choose.trans
      (relativeFunctorOverPre_isQCatEquivalence q.hom f ef).choose.symm

end SerrePositivity.InfinityCategories
