module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedComparisonProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceTriangleCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedSectionEquivalence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 元の入力同値の指定二比較は、逆向きの三角整合性を満たす。 -/
lemma dgModuleResolvedSourceSectionEquivalence_comparison_symm :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).symm.homInvIso.postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).symm.invHomIso.precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F)) := by
  apply Iso.ext
  apply (Arrow.mk_injective _ _)
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso_projection_arrow R C E F
  have h₁ : Arrow.mk (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).homInvIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F))).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F))))) := by
    change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (eqToIso
      (congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C ↦
        HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSection_comp_source R C E F))) _).hom = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_eqToIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSection_comp_source R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F))]
    simp only [eqToIso.hom]
    rw [← Category.comp_id (eqToHom _), Arrow.arrow_mk_eqToHom_comp]
    rfl
  exact h₀.trans h₁.symm
/-- 元の入力同値の指定二比較は、元の向きの三角整合性も満たす。 -/
lemma dgModuleResolvedSourceSectionEquivalence_comparison :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).homInvIso.postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).invHomIso.precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).hom :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).symm.comparison_symm
    (dgModuleResolvedSourceSectionEquivalence_comparison_symm R C E F))
/-- 元の入力同値から作った随伴の余単位は、元の同じ指定比較の射。 -/
lemma dgModuleResolvedSourceSectionEquivalence_counitHom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).toAdjunction.counitHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso R C E F).hom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).toAdjunction_counitHom_of_comparison
    (dgModuleResolvedSourceSectionEquivalence_comparison R C E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
