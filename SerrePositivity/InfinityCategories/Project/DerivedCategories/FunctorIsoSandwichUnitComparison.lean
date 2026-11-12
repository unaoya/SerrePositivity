module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichCoherentUnits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoPrecompIdentity
/-!
概要：任意の後続比較を持つ恒等模型で coherent な左単位を回収する。
方針：指定余単位との三角式と h Fun の同じ交換則を使う。
規約：後続比較を恒等に限定しない。使われ方：cell 合成子の単位三角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_coherent_left_unit_comparison {A X C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Z] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A X)
    (N : A ⟶ C) (t : C ⟶ Z) (G : X ⟶ Z) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (e.inv ≫ N ≫ t)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor e.inv e.hom e.inv t e.coherentHomInvIso
      (𝟙 X) G (𝟙 A) N N e.invHomIso.symm b (Iso.refl _) = b := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_tail, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichTail,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_refl]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_refl ((𝟙 A ≫ N) ≫ t) e.inv]
  apply Iso.ext
  change (e.invHomIso.postcomp G).inv ≫
    (b.precomp (e.inv ≫ 𝟙 A ≫ e.hom)).hom ≫
      ((e.coherentHomInvIso.postcomp (N ≫ t)).precomp (e.inv ≫ 𝟙 A)).hom ≫ 𝟙 _ = b.hom
  simp only [Category.comp_id]
  have h := congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp a (N ≫ t))
    e.coherentHomInvIso_pre_inv
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp] at h
  have hc : (e.coherentHomInvIso.postcomp (N ≫ t)).precomp (e.inv ≫ 𝟙 A) =
      e.invHomIso.postcomp (e.inv ≫ N ≫ t) := by
    simpa only [Category.comp_id, Category.assoc] using! h
  rw [hc]
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange e.invHomIso.symm b
  have hx' : (e.invHomIso.postcomp G).inv ≫ (b.precomp (e.inv ≫ e.hom)).hom =
      b.hom ≫ (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).inv := by
    simpa only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, Iso.symm_hom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id] using! congrArg Iso.hom hx
  have hn : (e.invHomIso.postcomp G).inv ≫ (b.precomp (e.inv ≫ e.hom)).hom ≫
      (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).hom = b.hom := by
    have hh := congrArg (fun z ↦ z ≫
      (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).hom) hx'
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using! hh
  simpa only [Category.id_comp] using! hn
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
