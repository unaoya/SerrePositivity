module
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceCoherentHomInv
/-!
概要：指定 invHomIso と coherent な反対側の比較の両三角式を照合する。
方針：指定された同型の値と関手 ∞ 圏の二胞体を保持する。
規約：古い比較との一致を先取りしない。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma QCatEquivalence.coherentHomInvIso_left_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    Bicategory.leftZigzagIso (f := qcatMap e.hom) (g := qcatMap e.inv)
        (functorIsoToQcatIso e.coherentHomInvIso.symm)
        (functorIsoToQcatIso e.invHomIso) =
      Bicategory.leftUnitor (qcatMap e.hom) ≪≫
        (Bicategory.rightUnitor (qcatMap e.hom)).symm := by
  rw [QCatEquivalence.coherentHomInvIso_unit,
    ← QCatEquivalence.adjointEquivalencePreservingCounit_counit]
  exact e.adjointEquivalencePreservingCounit.left_triangle
lemma QCatEquivalence.coherentHomInvIso_right_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    Bicategory.rightZigzagIso (f := qcatMap e.hom) (g := qcatMap e.inv)
        (functorIsoToQcatIso e.coherentHomInvIso.symm)
        (functorIsoToQcatIso e.invHomIso) =
      Bicategory.rightUnitor (qcatMap e.inv) ≪≫
        (Bicategory.leftUnitor (qcatMap e.inv)).symm := by
  rw [QCatEquivalence.coherentHomInvIso_unit,
    ← QCatEquivalence.adjointEquivalencePreservingCounit_counit]
  exact e.adjointEquivalencePreservingCounit.right_triangle
end
end SerrePositivity.InfinityCategories
