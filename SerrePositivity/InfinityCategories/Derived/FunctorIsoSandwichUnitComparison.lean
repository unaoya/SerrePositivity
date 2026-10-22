module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichCoherentUnits
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompIdentity
/-!
概要：任意の後続比較を持つ恒等模型で coherent な左単位を回収する。
方針：指定余単位との三角式と h Fun の同じ交換則を使う。
規約：後続比較を恒等に限定しない。使われ方：cell 合成子の単位三角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_coherent_left_unit_comparison {A X C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Z] (e : QCatEquivalence A X)
    (N : A ⟶ C) (t : C ⟶ Z) (G : X ⟶ Z) (b : FunctorIso G (e.inv ≫ N ≫ t)) :
    functorIsoSandwichCompositor e.inv e.hom e.inv t e.coherentHomInvIso
      (𝟙 X) G (𝟙 A) N N e.invHomIso.symm b (Iso.refl _) = b := by
  simp only [functorIsoSandwichCompositor_tail, functorIsoSandwichTail,
    F2.functorIso_precomp_trans, F2.functorIso_precomp_precomp,
    F2.functorIso_postcomp_symm, functorIso_postcomp_refl]
  rw [functorIso_precomp_refl ((𝟙 A ≫ N) ≫ t) e.inv]
  apply Iso.ext
  change (e.invHomIso.postcomp G).inv ≫
    (b.precomp (e.inv ≫ 𝟙 A ≫ e.hom)).hom ≫
      ((e.coherentHomInvIso.postcomp (N ≫ t)).precomp (e.inv ≫ 𝟙 A)).hom ≫ 𝟙 _ = b.hom
  simp only [Category.comp_id]
  have h := congrArg (fun a ↦ FunctorIso.postcomp a (N ≫ t))
    e.coherentHomInvIso_pre_inv
  simp only [F2.functorIso_precomp_postcomp, F2.functorIso_postcomp_postcomp] at h
  have hc : (e.coherentHomInvIso.postcomp (N ≫ t)).precomp (e.inv ≫ 𝟙 A) =
      e.invHomIso.postcomp (e.inv ≫ N ≫ t) := by
    simpa only [Category.comp_id, Category.assoc] using! h
  rw [hc]
  have hx := F2.functorIso_whisker_exchange e.invHomIso.symm b
  have hx' : (e.invHomIso.postcomp G).inv ≫ (b.precomp (e.inv ≫ e.hom)).hom =
      b.hom ≫ (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).inv := by
    simpa only [Iso.trans_hom, F2.functorIso_postcomp_symm, Iso.symm_hom,
      functorIso_precomp_id] using! congrArg Iso.hom hx
  have hn : (e.invHomIso.postcomp G).inv ≫ (b.precomp (e.inv ≫ e.hom)).hom ≫
      (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).hom = b.hom := by
    have hh := congrArg (fun z ↦ z ≫
      (e.invHomIso.postcomp (e.inv ≫ N ≫ t)).hom) hx'
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using! hh
  simpa only [Category.id_comp] using! hn
end
end SerrePositivity.InfinityCategories
