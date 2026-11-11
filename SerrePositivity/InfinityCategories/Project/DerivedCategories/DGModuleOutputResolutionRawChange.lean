module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionReplacementUnlift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedChangeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolutionOutputPostcompositionTransport
/-!
概要：元の出力分解と変更同型の指定値を、同じ raw 出力射影へ回収する。
方針：出力宇宙の上げ下げと指定出力比較の後合成則だけを使う。
規約：元の入力切断と変更比較を保持。使われ方：導来射作用との共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
  (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
def dgModuleOutputResolution_rawChangeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E G).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E G)) := by
  have hS := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor_sourceLift R C E a hs hq ha)
  have hR := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor_replacement R C E a hs hq ha)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hS hR
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E a hs hq ha))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E G)) hS hR
lemma dgModuleOutputResolution_changeIso_down_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso R C E a hs hq ha).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))))
      (dgModuleOutputResolution_rawChangeIso R C E a hs hq ha) := by
  have hS := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor_sourceLift R C E a hs hq ha)
  have hR := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor_replacementLift R C E a hs hq ha)
  have hR' := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor_replacement R C E a hs hq ha)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hS hR hR'
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso dgModuleOutputResolution_rawChangeIso
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso_postcomp_heq_of_outputs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E a hs hq ha))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R C E F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R C E G))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E G)) hS hR hR'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift_down R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift_down R C E G)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
