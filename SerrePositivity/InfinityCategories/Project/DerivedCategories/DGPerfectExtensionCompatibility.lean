module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectExtensionInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDerivedFunctor
/-!
概要：Perf の実 tensor と D(D) の実 tensor は、同じ全関手圏の比較四角形を持つ。
方針：射影的模型への二つの包含の厳密な dg 可換性と、同じ余単位を使う。
規約：対象別比較ではない。使われ方：β5 の Perf と D(A) の関手性の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- Perf の包含と graph tensor の比較は、同じ実 ∞ 関手の全関手同型で可換。 -/
def dgPerfectExtensionInclusionIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R D E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D E F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R E) := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E (dgModuleExtension R D E F)
    (fun _ h => _root_.SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective R D E F h)
  have hd : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D).comp L =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R E) := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    change (𝟙 _ ≫ (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension R D E F).map x.val y.val) ≫ eqToHom _ =
      (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension R D E F).map x.val y.val ≫ 𝟙 _
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R E) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) hd
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.invHomIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D))
  have h := h₀.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R E)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv)
  rw [← he]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor,
    Category.assoc, Category.comp_id] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
