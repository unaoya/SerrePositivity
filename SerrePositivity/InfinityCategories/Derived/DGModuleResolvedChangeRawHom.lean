module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorFields
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
variable {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))
lemma dgModuleOutputResolution_rawChangeIso_hom :
    (dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).hom =
      (dgModuleOutputResolution_rawFactorPrecompIso R C E F).hom ≫ (functorHomPostcomp
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G))
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u +
      1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))
      ≫ (dgModuleOutputResolution_rawFactorPrecompIso R C E G).inv := by
  have hn := dgModuleResolutionChangeIdentity_comparison_hom R C E F G a hs hq ha
  change (dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).hom =
    (dgModuleOutputResolution_rawFactorPrecompIso R C E F).hom ≫ (functorHomPostcomp
    (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E G))
    ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R (DGUniverseLift.{max
    (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
    E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))) ≫
    (dgModuleOutputResolution_rawFactorPrecompIso R C E G).inv at hn
  exact hn
lemma dgModuleResolvedInfinity_changeIso_hom_raw_heq :
    HEq (dgModuleResolvedInfinity_changeIso R C E a hs hq ha).hom
      (((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).hom ≫ (functorHomPrecomp
      ((dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))) ((dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)) ≫
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))) (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) (functorHomPostcomp (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G))
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u +
      1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))) ≫
      ((dgModuleOutputResolution_rawFactorPrecompIso R C E G).precomp (dgNerve.map
        (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).inv) := by
  have hc := functorIso_hom_heq_of_endpoint_heq (dgModuleResolvedInfinity_changeIso R C E a hs
    hq ha) ((dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).precomp (dgNerve.map
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
    (dgModuleResolvedInfinity_eq_section_replacement R C E F)
    (dgModuleResolvedInfinity_eq_section_replacement R C E G)
    (dgModuleResolvedInfinity_changeIso_raw_heq R C E a hs hq ha)
  have hp := functorHom_conjugation_precomp (dgModuleOutputResolution_rawChangeIso R C E a hs hq
    ha) (dgModuleOutputResolution_rawFactorPrecompIso R C E F)
    (dgModuleOutputResolution_rawFactorPrecompIso R C E G) (functorHomPostcomp (dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E G))
    ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R (DGUniverseLift.{max
    (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
    E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))
    (dgModuleOutputResolution_rawChangeIso_hom R C E a hs hq ha) (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  exact hc.trans (heq_of_eq hp)
end SerrePositivity.InfinityCategories
