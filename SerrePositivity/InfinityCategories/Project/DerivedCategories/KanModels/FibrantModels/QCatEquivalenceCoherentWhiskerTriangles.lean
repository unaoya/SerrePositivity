module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.QCatHomWhiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.QCatEquivalenceCoherentTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.QCatEquivalenceHomInvCorrection
/-!
概要：指定余単位を保つ両三角式を h Fun の前後合成 API で公開する。
方針：双圏の実 whiskering と内部 Hom の実作用の一致を使う。
規約：旧比較の補正を明示する。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma QCatEquivalence.coherentHomInvIso_post_hom_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.coherentHomInvIso.symm e.hom ≪≫ e.invHomIso.precomp e.hom =
      Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e.hom)) := by
  apply Iso.ext
  have h := congrArg Iso.hom e.coherentHomInvIso_left_triangle
  have hh := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map) h
  simp only [Bicategory.leftZigzagIso_hom] at hh
  dsimp only [Bicategory.leftZigzag, bicategoricalComp] at hh
  simp only [CategoryTheory.Functor.map_comp] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qcatHomFunctor_map_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qcatHomFunctor_map_whiskerLeft] at hh
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso, Iso.trans_hom, Iso.symm_hom] at hh
  dsimp only [BicategoricalCoherence.iso] at hh
  simp only [hoFunctor_obj, Cat.of_α, ObjectProperty.homMk_hom,
    Bicategory.Strict.associator_eqToIso, eqToIso_refl, Bicategory.whiskerRightIso,
    Iso.refl_hom, Bicategory.whiskerRight_comp, Iso.refl_inv, Bicategory.id_whiskerRight,
    Category.comp_id, Iso.refl_trans, CategoryTheory.Functor.map_id, Category.id_comp,
    Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso] at hh
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (𝟙 X) (e.hom ≫ e.inv) e.hom e.coherentHomInvIso.inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (e.inv ≫ e.hom) (𝟙 Y) e.hom e.invHomIso.hom = 𝟙 _ at hh
  simpa only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed, Iso.symm_hom, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using! hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_post_hom_triangle)

lemma QCatEquivalence.coherentHomInvIso_pre_inv_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.coherentHomInvIso.symm e.inv ≪≫ e.invHomIso.postcomp e.inv =
      Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e.inv)) := by
  apply Iso.ext
  have h := congrArg Iso.hom e.coherentHomInvIso_right_triangle
  have hh := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map) h
  simp only [Bicategory.rightZigzagIso_hom] at hh
  dsimp only [Bicategory.rightZigzag, bicategoricalComp] at hh
  simp only [CategoryTheory.Functor.map_comp] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qcatHomFunctor_map_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qcatHomFunctor_map_whiskerRight] at hh
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso, Iso.trans_hom, Iso.symm_hom] at hh
  dsimp only [BicategoricalCoherence.iso] at hh
  simp only [hoFunctor_obj, Cat.of_α, ObjectProperty.homMk_hom,
    Bicategory.whiskerRightIso, Iso.refl_hom, Bicategory.whiskerRight_comp,
    Bicategory.Strict.associator_eqToIso, eqToIso_refl, Iso.refl_inv,
    Bicategory.id_whiskerRight, Category.comp_id, Iso.refl_symm, Iso.trans_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, Bicategory.Strict.rightUnitor_eqToIso,
    Bicategory.Strict.leftUnitor_eqToIso, Category.id_comp] at hh
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv] at hh
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (𝟙 X) (e.hom ≫ e.inv) e.inv e.coherentHomInvIso.inv ≫
    𝟙 _ ≫ 𝟙 _ ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (e.inv ≫ e.hom) (𝟙 Y) e.inv e.invHomIso.hom = 𝟙 _ at hh
  simp only [Category.id_comp] at hh
  simpa only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed, Iso.symm_hom, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using! hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_pre_inv_triangle)

lemma QCatEquivalence.coherentHomInvIso_post_hom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.coherentHomInvIso.postcomp e.hom = e.invHomIso.precomp e.hom := by
  have h := congrArg (fun a ↦ e.coherentHomInvIso.postcomp e.hom ≪≫ a)
    e.coherentHomInvIso_post_hom_triangle
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, Iso.self_symm_id_assoc] at h
  exact (Iso.trans_refl (e.coherentHomInvIso.postcomp e.hom)).symm.trans h.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_post_hom)

lemma QCatEquivalence.coherentHomInvIso_pre_inv {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.coherentHomInvIso.precomp e.inv = e.invHomIso.postcomp e.inv := by
  have h := congrArg (fun a ↦ e.coherentHomInvIso.precomp e.inv ≪≫ a)
    e.coherentHomInvIso_pre_inv_triangle
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm, Iso.self_symm_id_assoc] at h
  exact (Iso.trans_refl (e.coherentHomInvIso.precomp e.inv)).symm.trans h.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (coherentHomInvIso_pre_inv)

lemma QCatEquivalence.homInvCorrectionIso_post_hom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.homInvIso.postcomp e.hom ≪≫ e.homInvCorrectionIso.postcomp e.hom =
      e.invHomIso.precomp e.hom := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, e.homInvCorrectionIso_factor,
    e.coherentHomInvIso_post_hom]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (homInvCorrectionIso_post_hom)

lemma QCatEquivalence.homInvCorrectionIso_pre_inv {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.homInvIso.precomp e.inv ≪≫ e.homInvCorrectionIso.precomp e.inv =
      e.invHomIso.postcomp e.inv := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, e.homInvCorrectionIso_factor,
    e.coherentHomInvIso_pre_inv]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (homInvCorrectionIso_pre_inv)

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
