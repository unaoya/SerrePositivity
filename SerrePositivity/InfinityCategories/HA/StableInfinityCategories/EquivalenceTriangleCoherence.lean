module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjointifyCounitCoherence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionHomTriangles
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction
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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Bicategory
open MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 指定二比較の三角整合性から、元の双圏同値の左三角式を得る。 -/
lemma QCatEquivalence.left_triangle_of_comparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    leftZigzagIso (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.homInvIso.symm) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.invHomIso) =
      (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom)) ≪≫ (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom)).symm := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag e.homInvIso.symm.hom e.invHomIso.hom =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e.hom)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag
    change (SSet.mapHomotopyCategory ((ihom X).map e.hom)).map e.homInvIso.symm.hom ≫
      (SSet.mapHomotopyCategory ((pre e.hom).app Y)).map e.invHomIso.hom = 𝟙 _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom e.homInvIso.symm e.hom,
      ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom e.invHomIso e.hom,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm]
    rw [h]
    exact Iso.inv_hom_id _
  apply Iso.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map_injective
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map
    (leftZigzag (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.inv)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv)).symm e.homInvIso.symm.hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (e.inv ≫ e.hom) (𝟙 Y)).symm e.invHomIso.hom)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatLeftZigzag_hom, hz]
  simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap e.hom)).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (left_triangle_of_comparison)


/-- 三角整合性を持つ同値の adjointification は、元の指定余単位を保持する。 -/
lemma QCatEquivalence.adjointEquivalence_counit_of_comparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    e.adjointEquivalence.counit = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e.invHomIso :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.bicategoryAdjointifyCounit_eq_of_left_triangle _ _ (e.left_triangle_of_comparison h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (adjointEquivalence_counit_of_comparison)


/-- 同値から作る随伴の単位は、元の指定比較の逆射。 -/
lemma QCatEquivalence.toAdjunction_unitHom
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.toAdjunction.unitHom = e.homInvIso.inv := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (e.hom ≫ e.inv)).symm e.homInvIso.inv) = _
  exact Equiv.apply_symm_apply _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (toAdjunction_unitHom)


/-- 三角整合性を持つ同値から作る随伴は、元の指定余単位を回収する。 -/
lemma QCatEquivalence.toAdjunction_counitHom_of_comparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    e.toAdjunction.counitHom = e.invHomIso.hom := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (e.inv ≫ e.hom) (𝟙 Y)) e.adjointEquivalence.counit.hom = _
  rw [e.adjointEquivalence_counit_of_comparison h]
  exact Equiv.apply_symm_apply _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (toAdjunction_counitHom_of_comparison)


/-- 指定二比較の三角整合性は、同じ同値を反対向きに使っても成り立つ。 -/
lemma QCatEquivalence.comparison_symm
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y)
    (h : e.homInvIso.postcomp e.hom = e.invHomIso.precomp e.hom) :
    e.symm.homInvIso.postcomp e.inv = e.symm.invHomIso.precomp e.inv := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_rightTriangleHom e.toAdjunction
  rw [e.toAdjunction_unitHom, e.toAdjunction_counitHom_of_comparison h] at ht
  change (SSet.mapHomotopyCategory ((pre e.inv).app X)).map e.homInvIso.symm.hom ≫
    (SSet.mapHomotopyCategory ((ihom Y).map e.inv)).map e.invHomIso.hom = 𝟙 _ at ht
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm] at ht
  apply Iso.ext
  have he := congrArg (fun z ↦ (e.homInvIso.precomp e.inv).hom ≫ z) ht
  simp only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp] at he
  change (e.invHomIso.postcomp e.inv).hom =
    (e.homInvIso.precomp e.inv).hom ≫ 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e.inv)) at he
  exact he.trans (Category.comp_id _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (comparison_symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
