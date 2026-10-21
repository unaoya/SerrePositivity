module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorRawValue
/-!
概要：持ち上げた元の入力変換を、同じ raw nerve 射の恒等出力分解後合成へ戻す。
方針：全前後合成の交換則と同じ上げ下げの恒等関係を使う。
規約：全関手射の同じ値を保持。使われ方：公開変更同型の共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (F G : DGFunctor R C (RightModule R E))
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, (F.comp (DGFunctor.id (RightModule R E))).map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    (G.comp (DGFunctor.id (RightModule R E))).map x y ≫
      eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
lemma dgModuleResolutionChangeIdentity_lifted_original_up_heq :
    HEq (functorHomPrecomp (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) (dgStrictNatTransNerveHom R
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u
      + 1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))
      (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
        (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) := by
  have hf : (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) = (dgNerve.map
    (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (dgNerve.map F) ≫
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [dgModuleResolutionLiftedInputFunctor, dgNerve.map_comp]
  have hg : (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) = (dgNerve.map
    (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (dgNerve.map G) ≫
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [dgModuleResolutionLiftedInputFunctor, dgNerve.map_comp]
  have hp := functorHom_precomp_heq (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v,
    max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
    (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
    (functorHomPrecomp ((dgNerve.map F) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max
      (u + 1) v} R (RightModule R E)))) ((dgNerve.map G) ≫ (dgNerve.map (dgUniverseLiftUp.{u,
      max (u + 1) v, max (u + 1) v} R (RightModule R E)))) (dgNerve.map (dgUniverseLiftDown.{u,
      max (u + 1) v, max (u + 1) v} R C))
      (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
        (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))))
    hf hg (dgModuleResolutionChangeIdentity_lifted_original_nerve_heq R C E F G a ha)
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  have hq := heq_of_eq (functorHomPrecomp_precomp
    ((dgNerve.map F) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
      (RightModule R E)))) ((dgNerve.map G) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v,
      max (u + 1) v} R (RightModule R E)))) (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v,
      max (u + 1) v} R C)) (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
    (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
      (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))))
  have hud := congrArg (fun H => dgNerve.map H)
    (dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R C)
  simp only [dgNerve.map_comp, dgNerve.map_id] at hud
  have hr := functorHomPrecomp_heq_of_source_eq
    (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
      (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) hud
  have ht := heq_of_eq (functorHom_precomp_id
    (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
      (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))))
  exact hp.trans (hq.trans (hr.trans ht))
lemma dgModuleResolutionChangeIdentity_lifted_action_up_heq :
    HEq (functorHomPrecomp ((dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))) ((dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)) ≫
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))) (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
      (functorHomPostcomp (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
        (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))
        ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
        (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
        (RightModule R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R
        (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max
        (u + 1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G
        a ha))))
      (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgModuleResolvedInfinity R
        (RightModule R E) E (DGFunctor.id (RightModule R E))) (dgStrictNatTransNerveHom R C
        (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) := by
  have h₀ := (heq_of_eq (functorHomPrecomp_postcomp
    (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map (dgUniverseLiftUp.{u, max (u
      + 1) v, max (u + 1) v} R C)) ((dgModuleFunctorResolutionSourceNerveEquivalence R
      (RightModule R E) E (DGFunctor.id (RightModule R E))).inv ≫ (dgNerve.map
      (dgModuleFunctorResolutionReplacement R (RightModule R E) E (DGFunctor.id (RightModule R
      E))))) (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
      (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))).symm
  have h₁ := functorHomPostcomp_heq
    (functorHomPrecomp (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) (dgStrictNatTransNerveHom R
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u
      + 1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)))
    (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
      (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))
    (dgModuleResolutionLiftedInputFunctor_up_eq R C E F)
    (dgModuleResolutionLiftedInputFunctor_up_eq R C E G)
    (dgModuleResolutionChangeIdentity_lifted_original_up_heq R C E F G a ha)
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))))
  have h₂ := heq_of_eq (functorHomPostcomp_postcomp (dgNerve.map F) (dgNerve.map G)
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)))
    ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R C (RightModule R E)
    (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))
  have hL := dgModuleResolvedInfinity_eq_section_replacement R (RightModule R E) E
    (DGFunctor.id (RightModule R E))
  have h₃ := functorHomPostcomp_heq_of_target_eq (dgStrictNatTransNerveHom R C (RightModule R
    E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)) hL.symm
  exact h₀.trans (h₁.trans (h₂.trans h₃))
end SerrePositivity.InfinityCategories
