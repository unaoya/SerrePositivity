module
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
/-!
概要：実 ∞ 圏同値の指定 invHomIso を保ったまま三角式付き同値を構成する。
方針：逆方向の同値を adjointify し、逆同型と右三角式で向きを戻す。
規約：元の homInvIso との一致は主張しない。使われ方：cell 比較の単位整合性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
def QCatEquivalence.adjointEquivalencePreservingCounit {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    Bicategory.Equivalence (qcatOf X) (qcatOf Y) where
  hom := qcatMap e.hom
  inv := qcatMap e.inv
  unit := e.symm.adjointEquivalence.counit.symm
  counit := e.symm.adjointEquivalence.unit.symm
  left_triangle := by
    have h := congrArg Iso.symm e.symm.adjointEquivalence.right_triangle
    simpa only [Bicategory.rightZigzagIso_symm, Iso.trans_symm, Iso.symm_symm_eq] using! h
lemma QCatEquivalence.adjointEquivalencePreservingCounit_counit {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.adjointEquivalencePreservingCounit.counit = functorIsoToQcatIso e.invHomIso := by
  change (functorIsoToQcatIso e.invHomIso.symm).symm = _
  apply Iso.ext
  rfl
end
end SerrePositivity.InfinityCategories
