module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedComparisonProjection
public import SerrePositivity.InfinityCategories.Stable.EquivalenceTriangleCoherence
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionEquivalence
/-!
概要：元の入力同値の指定二比較は三角式を満たし、随伴の余単位は元の比較そのもの。
方針：実 fiber の射影の恒等性と、同じ宇宙比較・端点輸送を使う。
規約：元の指定同型と実切断を保持する。使われ方：kernel の指定余単位の厳密回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 元の入力同値の指定二比較は、逆向きの三角整合性を満たす。 -/
lemma dgModuleResolvedSourceSectionEquivalence_comparison_symm :
    (dgModuleResolvedSourceSectionEquivalence R C E F).symm.homInvIso.postcomp
        (dgNerve.map (dgModuleFunctorResolutionSource R C E F)) =
      (dgModuleResolvedSourceSectionEquivalence R C E F).symm.invHomIso.precomp
        (dgNerve.map (dgModuleFunctorResolutionSource R C E F)) := by
  apply Iso.ext
  apply (Arrow.mk_injective _ _)
  have h₀ := dgModuleResolvedProjectionSectionIso_projection_arrow R C E F
  have h₁ : Arrow.mk (((dgModuleResolvedSourceSectionEquivalence R C E F).homInvIso.precomp
      (dgNerve.map (dgModuleFunctorResolutionSource R C E F))).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
        (dgNerve.map (dgModuleFunctorResolutionSource R C E F))))) := by
    change Arrow.mk (FunctorIso.precomp (eqToIso
      (congrArg (fun f : dgNerve R C ⟶ dgNerve R C ↦
        HomotopyCategory.mk (functorVertex f))
        (dgModuleResolvedSourceSection_comp_source R C E F))) _).hom = _
    rw [FunctorIso.precomp_eqToIso
      (dgModuleResolvedSourceSection_comp_source R C E F)
      (dgNerve.map (dgModuleFunctorResolutionSource R C E F))]
    simp only [eqToIso.hom]
    rw [← Category.comp_id (eqToHom _), Arrow.arrow_mk_eqToHom_comp]
    rfl
  exact h₀.trans h₁.symm
/-- 元の入力同値の指定二比較は、元の向きの三角整合性も満たす。 -/
lemma dgModuleResolvedSourceSectionEquivalence_comparison :
    (dgModuleResolvedSourceSectionEquivalence R C E F).homInvIso.postcomp
        (dgModuleResolvedSourceSectionEquivalence R C E F).hom =
      (dgModuleResolvedSourceSectionEquivalence R C E F).invHomIso.precomp
        (dgModuleResolvedSourceSectionEquivalence R C E F).hom :=
  ((dgModuleResolvedSourceSectionEquivalence R C E F).symm.comparison_symm
    (dgModuleResolvedSourceSectionEquivalence_comparison_symm R C E F))
/-- 元の入力同値から作った随伴の余単位は、元の同じ指定比較の射。 -/
lemma dgModuleResolvedSourceSectionEquivalence_counitHom :
    (dgModuleResolvedSourceSectionEquivalence R C E F).toAdjunction.counitHom =
      (dgModuleResolvedProjectionSectionIso R C E F).hom :=
  (dgModuleResolvedSourceSectionEquivalence R C E F).toAdjunction_counitHom_of_comparison
    (dgModuleResolvedSourceSectionEquivalence_comparison R C E F)
end SerrePositivity.InfinityCategories
