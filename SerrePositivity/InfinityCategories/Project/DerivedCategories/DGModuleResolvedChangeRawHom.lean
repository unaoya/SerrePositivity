module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactorFields
/-!
概要：指定済みの実出力分解の比較の射を、同じ元の nerve 作用へ照合する。
方針：全関手射の上げ下げと指定逆を保つ共役式を使う。
規約：比較の値を再選択しない。使われ方：導来 kernel の準同型比較の自然性。
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
lemma dgModuleOutputResolution_rawChangeIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u +
      1) v} (RightModule R E)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))
      ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E G).inv := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_comparison_hom R C E F G a hs hq ha
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max
    (u + 1) v, max (u + 1) v} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
    E)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E G).inv at hn
  exact hn
lemma dgModuleResolvedInfinity_changeIso_hom_raw_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso R C E a hs hq ha).hom
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u +
      1) v} (RightModule R E)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E G).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).inv) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso R C E a hs
    hq ha) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R C E G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso_raw_heq R C E a hs hq ha)
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_conjugation_precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawChangeIso R C E a hs hq
    ha) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max
    (u + 1) v, max (u + 1) v} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
    E)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))
    (dgModuleOutputResolution_rawChangeIso_hom R C E a hs hq ha) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  exact hc.trans (heq_of_eq hp)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
