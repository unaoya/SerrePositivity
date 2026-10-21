module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedChangeRawHom
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
lemma dgModuleResolvedInfinity_rawFactor_conjugation_raw_heq :
    HEq (((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
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
      1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a
      ha)))) ≫ ((dgModuleOutputResolution_rawFactorPrecompIso R C E G).precomp (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).inv)
      ((dgModuleResolvedInfinity_rawFactorIso R C E F).hom ≫ (functorHomPostcomp (dgNerve.map F)
        (dgNerve.map G) (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id
        (RightModule R E))) (dgStrictNatTransNerveHom R C (RightModule R E)
        (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) ≫
        (dgModuleResolvedInfinity_rawFactorIso R C E G).inv) := by
  have hf := dgModuleResolvedInfinity_eq_section_replacement R C E F
  have hg := dgModuleResolvedInfinity_eq_section_replacement R C E G
  have htf := dgModuleResolvedInfinity_rawFactor_target_eq R C E F
  have htg := dgModuleResolvedInfinity_rawFactor_target_eq R C E G
  have hp := dgModuleResolvedInfinity_rawFactor_hom_raw_heq R C E F
  have hqi := dgModuleResolvedInfinity_rawFactor_inv_raw_heq R C E G
  have hm := dgModuleResolutionChangeIdentity_lifted_action_up_heq R C E F G a ha
  have hLeft := functorHom_comp_heq ((dgModuleOutputResolution_rawFactorPrecompIso R C E
    F).precomp (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).hom
    (functorHomPrecomp ((dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
    ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E)))))) ((dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E G)) ≫
    ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E)))))) (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1)
    v, max (u + 1) v} R C)) (functorHomPostcomp (dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E G))
    ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R (DGUniverseLift.{max
    (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
    E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))))
    (dgModuleResolvedInfinity_rawFactorIso R C E F).hom (functorHomPostcomp (dgNerve.map F)
    (dgNerve.map G) (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R
    E))) (dgStrictNatTransNerveHom R C (RightModule R E)
    (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))
    hf.symm htf.symm htg.symm hp.symm hm
  have hAll := functorHom_comp_heq
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
      1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a
      ha))))) ((dgModuleOutputResolution_rawFactorPrecompIso R C E G).precomp (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).inv
    ((dgModuleResolvedInfinity_rawFactorIso R C E F).hom ≫ (functorHomPostcomp (dgNerve.map F)
      (dgNerve.map G) (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule
      R E))) (dgStrictNatTransNerveHom R C (RightModule R E)
      (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))))
      (dgModuleResolvedInfinity_rawFactorIso R C E G).inv hf.symm htg.symm hg.symm hLeft hqi.symm
  simpa only [Category.assoc] using! hAll
end SerrePositivity.InfinityCategories
