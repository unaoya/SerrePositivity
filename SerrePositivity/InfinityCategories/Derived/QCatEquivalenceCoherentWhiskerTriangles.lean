module
public import SerrePositivity.InfinityCategories.Derived.QCatHomWhiskering
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceCoherentTriangles
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceHomInvCorrection
/-!
概要：指定余単位を保つ両三角式を h Fun の前後合成 API で公開する。
方針：双圏の実 whiskering と内部 Hom の実作用の一致を使う。
規約：旧比較の補正を明示する。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma QCatEquivalence.coherentHomInvIso_post_hom_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    FunctorIso.postcomp e.coherentHomInvIso.symm e.hom ≪≫ e.invHomIso.precomp e.hom =
      Iso.refl (HomotopyCategory.mk (functorVertex e.hom)) := by
  apply Iso.ext
  have h := congrArg Iso.hom e.coherentHomInvIso_left_triangle
  have hh := congrArg ((qcatHomFunctor X Y).map) h
  simp only [Bicategory.leftZigzagIso_hom] at hh
  dsimp only [Bicategory.leftZigzag, bicategoricalComp] at hh
  simp only [CategoryTheory.Functor.map_comp] at hh
  rw [qcatHomFunctor_map_whiskerRight, qcatHomFunctor_map_whiskerLeft] at hh
  dsimp only [functorIsoToQcatIso, Iso.trans_hom, Iso.symm_hom] at hh
  dsimp only [BicategoricalCoherence.iso] at hh
  simp only [hoFunctor_obj, Cat.of_α, ObjectProperty.homMk_hom,
    Bicategory.Strict.associator_eqToIso, eqToIso_refl, Bicategory.whiskerRightIso,
    Iso.refl_hom, Bicategory.whiskerRight_comp, Iso.refl_inv, Bicategory.id_whiskerRight,
    Category.comp_id, Iso.refl_trans, CategoryTheory.Functor.map_id, Category.id_comp,
    Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso] at hh
  change functorHomPostcomp (𝟙 X) (e.hom ≫ e.inv) e.hom e.coherentHomInvIso.inv ≫
    functorHomPrecomp (e.inv ≫ e.hom) (𝟙 Y) e.hom e.invHomIso.hom = 𝟙 _ at hh
  simpa only [Iso.trans_hom, functorIso_postcomp_hom_typed,
    functorIso_precomp_hom_typed, Iso.symm_hom, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using! hh
lemma QCatEquivalence.coherentHomInvIso_pre_inv_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    FunctorIso.precomp e.coherentHomInvIso.symm e.inv ≪≫ e.invHomIso.postcomp e.inv =
      Iso.refl (HomotopyCategory.mk (functorVertex e.inv)) := by
  apply Iso.ext
  have h := congrArg Iso.hom e.coherentHomInvIso_right_triangle
  have hh := congrArg ((qcatHomFunctor Y X).map) h
  simp only [Bicategory.rightZigzagIso_hom] at hh
  dsimp only [Bicategory.rightZigzag, bicategoricalComp] at hh
  simp only [CategoryTheory.Functor.map_comp] at hh
  rw [qcatHomFunctor_map_whiskerLeft, qcatHomFunctor_map_whiskerRight] at hh
  dsimp only [functorIsoToQcatIso, Iso.trans_hom, Iso.symm_hom] at hh
  dsimp only [BicategoricalCoherence.iso] at hh
  simp only [hoFunctor_obj, Cat.of_α, ObjectProperty.homMk_hom,
    Bicategory.whiskerRightIso, Iso.refl_hom, Bicategory.whiskerRight_comp,
    Bicategory.Strict.associator_eqToIso, eqToIso_refl, Iso.refl_inv,
    Bicategory.id_whiskerRight, Category.comp_id, Iso.refl_symm, Iso.trans_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, Bicategory.Strict.rightUnitor_eqToIso,
    Bicategory.Strict.leftUnitor_eqToIso, Category.id_comp] at hh
  dsimp only [qcatHomFunctor, qcatCellEquiv] at hh
  change functorHomPrecomp (𝟙 X) (e.hom ≫ e.inv) e.inv e.coherentHomInvIso.inv ≫
    𝟙 _ ≫ 𝟙 _ ≫
    functorHomPostcomp (e.inv ≫ e.hom) (𝟙 Y) e.inv e.invHomIso.hom = 𝟙 _ at hh
  simp only [Category.id_comp] at hh
  simpa only [Iso.trans_hom, functorIso_postcomp_hom_typed,
    functorIso_precomp_hom_typed, Iso.symm_hom, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using! hh
lemma QCatEquivalence.coherentHomInvIso_post_hom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.coherentHomInvIso.postcomp e.hom = e.invHomIso.precomp e.hom := by
  have h := congrArg (fun a ↦ e.coherentHomInvIso.postcomp e.hom ≪≫ a)
    e.coherentHomInvIso_post_hom_triangle
  simp only [F2.functorIso_postcomp_symm, Iso.self_symm_id_assoc] at h
  exact (Iso.trans_refl (e.coherentHomInvIso.postcomp e.hom)).symm.trans h.symm
lemma QCatEquivalence.coherentHomInvIso_pre_inv {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.coherentHomInvIso.precomp e.inv = e.invHomIso.postcomp e.inv := by
  have h := congrArg (fun a ↦ e.coherentHomInvIso.precomp e.inv ≪≫ a)
    e.coherentHomInvIso_pre_inv_triangle
  simp only [F2.functorIso_precomp_symm, Iso.self_symm_id_assoc] at h
  exact (Iso.trans_refl (e.coherentHomInvIso.precomp e.inv)).symm.trans h.symm
lemma QCatEquivalence.homInvCorrectionIso_post_hom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.homInvIso.postcomp e.hom ≪≫ e.homInvCorrectionIso.postcomp e.hom =
      e.invHomIso.precomp e.hom := by
  rw [← F2.functorIso_postcomp_trans, e.homInvCorrectionIso_factor,
    e.coherentHomInvIso_post_hom]
lemma QCatEquivalence.homInvCorrectionIso_pre_inv {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.homInvIso.precomp e.inv ≪≫ e.homInvCorrectionIso.precomp e.inv =
      e.invHomIso.postcomp e.inv := by
  rw [← F2.functorIso_precomp_trans, e.homInvCorrectionIso_factor,
    e.coherentHomInvIso_pre_inv]
end
end SerrePositivity.InfinityCategories
