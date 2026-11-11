module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalenceCoherentWhiskerTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichMiddleChange
/-!
概要：coherent な中間比較による一般 sandwich 合成子の両単位式。
方針：指定余単位の両消去式と同じ全関手同型の前後合成を使う。
規約：恒等模型での計算。使われ方：指定 diagonal cell 模型の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIso_precomp_refl {W X Y : SSet.{u}} (f : X ⟶ Y) (p : W ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (f := f) (g := f) (Iso.refl _) p = Iso.refl _ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso, CategoryTheory.Functor.mapIso_refl]
  rfl
lemma functorIso_postcomp_refl {X Y Z : SSet.{u}} (f : X ⟶ Y) (p : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (f := f) (g := f) (Iso.refl _) p = Iso.refl _ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso, CategoryTheory.Functor.mapIso_refl]
  rfl

lemma functorIsoSandwichCompositor_coherent_left_unit {A X C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory X] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A X)
    (N : A ⟶ C) (t : C ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor e.inv e.hom e.inv t e.coherentHomInvIso
      (𝟙 X) (e.inv ≫ N ≫ t) (𝟙 A) N N
      e.invHomIso.symm (Iso.refl _) (Iso.refl _) = Iso.refl _ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_tail, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichTail,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, functorIso_precomp_refl, functorIso_postcomp_refl]
  rw [functorIso_precomp_refl ((𝟙 A ≫ e.hom) ≫ e.inv ≫ N ≫ t) e.inv,
    functorIso_precomp_refl ((𝟙 A ≫ N) ≫ t) e.inv]
  apply Iso.ext
  change (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).inv ≫
    𝟙 _ ≫ ((e.coherentHomInvIso.postcomp (N ≫ t)).precomp (e.inv ≫ 𝟙 A)).hom ≫
    𝟙 _ = 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  have h := congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp a (N ≫ t))
    e.coherentHomInvIso_pre_inv
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp] at h
  have hc : (e.coherentHomInvIso.postcomp (N ≫ t)).precomp (e.inv ≫ 𝟙 A) =
      e.invHomIso.postcomp (e.inv ≫ N ≫ t) := by
    simpa only [Category.comp_id, Category.assoc] using! h
  rw [hc]
  exact (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).inv_hom_id
lemma functorIsoSandwichCompositor_coherent_right_unit {X A B Y : SSet.{u}}
    [Quasicategory B] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence B Y)
    (s : X ⟶ A) (M : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s e.hom e.inv e.hom e.coherentHomInvIso
      (s ≫ M ≫ e.hom) (𝟙 Y) M (𝟙 B) M
      (Iso.refl _) e.invHomIso.symm (Iso.refl _) = Iso.refl _ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_tail, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichTail,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm, functorIso_postcomp_refl]
  rw [functorIso_precomp_refl ((M ≫ 𝟙 B) ≫ e.hom) s]
  apply Iso.ext
  change 𝟙 _ ≫ (e.invHomIso.precomp (s ≫ M ≫ e.hom)).inv ≫
    ((e.coherentHomInvIso.postcomp (𝟙 B ≫ e.hom)).precomp (s ≫ M)).hom ≫
    𝟙 _ = 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  have h := congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a (s ≫ M))
    e.coherentHomInvIso_post_hom
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp] at h
  have hc : (e.coherentHomInvIso.postcomp (𝟙 B ≫ e.hom)).precomp (s ≫ M) =
      e.invHomIso.precomp (s ≫ M ≫ e.hom) := by
    simpa only [Category.id_comp, Category.assoc] using! h
  rw [hc]
  exact (e.invHomIso.precomp (s ≫ M ≫ e.hom)).inv_hom_id
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
