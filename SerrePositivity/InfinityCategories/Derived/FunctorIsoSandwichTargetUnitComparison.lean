module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichUnitComparison
/-!
概要：任意の始域比較を持つ恒等模型で coherent な終域単位を回収する。
方針：指定余単位との三角式と同じ前後合成を使う。
規約：始域比較を恒等に限定しない。使われ方：cell 合成子の終域単位三角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_coherent_right_unit_comparison {X A B Y : SSet.{u}}
    [Quasicategory B] [Quasicategory Y] (e : QCatEquivalence B Y)
    (s : X ⟶ A) (M : A ⟶ B) (F : X ⟶ Y) (a : FunctorIso F (s ≫ M ≫ e.hom)) :
    functorIsoSandwichCompositor s e.hom e.inv e.hom e.coherentHomInvIso
      F (𝟙 Y) M (𝟙 B) M a e.invHomIso.symm (Iso.refl _) = a := by
  simp only [functorIsoSandwichCompositor_tail, functorIsoSandwichTail,
    F2.functorIso_precomp_trans, F2.functorIso_precomp_precomp,
    F2.functorIso_precomp_symm, F2.functorIso_postcomp_id, functorIso_postcomp_refl]
  rw [functorIso_precomp_refl ((M ≫ 𝟙 B) ≫ e.hom) s]
  apply Iso.ext
  change a.hom ≫ (e.invHomIso.precomp (s ≫ M ≫ e.hom)).inv ≫
    ((e.coherentHomInvIso.postcomp (𝟙 B ≫ e.hom)).precomp (s ≫ M)).hom ≫
    𝟙 _ = a.hom
  simp only [Category.comp_id]
  have h := congrArg (fun b ↦ FunctorIso.precomp b (s ≫ M))
    e.coherentHomInvIso_post_hom
  simp only [F2.functorIso_precomp_precomp] at h
  have hc : (e.coherentHomInvIso.postcomp (𝟙 B ≫ e.hom)).precomp (s ≫ M) =
      e.invHomIso.precomp (s ≫ M ≫ e.hom) := by
    simpa only [Category.id_comp, Category.assoc] using! h
  rw [hc]
  simp only [Iso.inv_hom_id, Category.comp_id]
end
end SerrePositivity.InfinityCategories
