module
public import SerrePositivity.InfinityCategories.Stable.AdjointifyCounitCoherence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionHomTriangles
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceAdjunction
/-!
概要：指定同値の全関手比較と、両向きの随伴の単位・余単位を厳密に照合する。
方針：実 fiber の射影の恒等性と、指定二比較の前後合成を照合する。
規約：元の指定射と同型を保持する。使われ方：入力分解の同じ余単位の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Bicategory
open MonoidalClosed SSet
open scoped Simplicial

/-- 指定二比較の三角整合性から、元の双圏同値の左三角式を得る。 -/
lemma QCatEquivalence.left_triangle_of_comparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    leftZigzagIso (f := qcatMap e.hom) (g := qcatMap e.inv)
      (functorIsoToQcatIso e.homInvIso.symm) (functorIsoToQcatIso e.invHomIso) =
      (λ_ (qcatMap e.hom)) ≪≫ (ρ_ (qcatMap e.hom)).symm := by
  have hz : unitLeftZigzag e.homInvIso.symm.hom e.invHomIso.hom =
      𝟙 (HomotopyCategory.mk (functorVertex e.hom)) := by
    unfold unitLeftZigzag
    change (SSet.mapHomotopyCategory ((ihom X).map e.hom)).map e.homInvIso.symm.hom ≫
      (SSet.mapHomotopyCategory ((pre e.hom).app Y)).map e.invHomIso.hom = 𝟙 _
    rw [← F2.functorIso_postcomp_hom e.homInvIso.symm e.hom,
      ← F2.functorIso_precomp_hom e.invHomIso e.hom,
      F2.functorIso_postcomp_symm]
    rw [h]
    exact Iso.inv_hom_id _
  apply Iso.ext
  apply (qcatHomFunctor X Y).map_injective
  change (qcatHomFunctor X Y).map
    (leftZigzag (f := qcatMap e.hom) (g := qcatMap e.inv)
      ((qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv)).symm e.homInvIso.symm.hom)
      ((qcatCellEquiv (e.inv ≫ e.hom) (𝟙 Y)).symm e.invHomIso.hom)) = _
  rw [qcatLeftZigzag_hom, hz]
  simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp]
  exact ((qcatHomFunctor X Y).map_id (qcatMap e.hom)).symm

/-- 三角整合性を持つ同値の adjointification は、元の指定余単位を保持する。 -/
lemma QCatEquivalence.adjointEquivalence_counit_of_comparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    e.adjointEquivalence.counit = functorIsoToQcatIso e.invHomIso :=
  bicategoryAdjointifyCounit_eq_of_left_triangle _ _ (e.left_triangle_of_comparison h)

/-- 同値から作る随伴の単位は、元の指定比較の逆射。 -/
lemma QCatEquivalence.toAdjunction_unitHom
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.toAdjunction.unitHom = e.homInvIso.inv := by
  change (qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv))
    ((qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv)).symm e.homInvIso.inv) = _
  exact Equiv.apply_symm_apply _ _

/-- 三角整合性を持つ同値から作る随伴は、元の指定余単位を回収する。 -/
lemma QCatEquivalence.toAdjunction_counitHom_of_comparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    e.toAdjunction.counitHom = e.invHomIso.hom := by
  change (qcatCellEquiv (e.inv ≫ e.hom) (𝟙 Y)) e.adjointEquivalence.counit.hom = _
  rw [e.adjointEquivalence_counit_of_comparison h]
  exact Equiv.apply_symm_apply _ _

/-- 指定二比較の三角整合性は、同じ同値を反対向きに使っても成り立つ。 -/
lemma QCatEquivalence.comparison_symm
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    e.symm.homInvIso.postcomp e.inv = e.symm.invHomIso.precomp e.inv := by
  have ht := SerrePositivity.InfinityCategories.F1B.adjunction_rightTriangleHom e.toAdjunction
  rw [e.toAdjunction_unitHom, e.toAdjunction_counitHom_of_comparison h] at ht
  change (SSet.mapHomotopyCategory ((pre e.inv).app X)).map e.homInvIso.symm.hom ≫
    (SSet.mapHomotopyCategory ((ihom Y).map e.inv)).map e.invHomIso.hom = 𝟙 _ at ht
  rw [← F2.functorIso_precomp_hom, ← F2.functorIso_postcomp_hom,
    F2.functorIso_precomp_symm] at ht
  apply Iso.ext
  have he := congrArg (fun z ↦ (e.homInvIso.precomp e.inv).hom ≫ z) ht
  simp only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp] at he
  change (e.invHomIso.postcomp e.inv).hom =
    (e.homInvIso.precomp e.inv).hom ≫ 𝟙 (HomotopyCategory.mk (functorVertex e.inv)) at he
  exact he.trans (Category.comp_id _)
end SerrePositivity.InfinityCategories
