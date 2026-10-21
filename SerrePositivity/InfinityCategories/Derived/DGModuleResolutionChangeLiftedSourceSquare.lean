module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionLiftedInput
/-!
概要：元の入力分解の対象宇宙を保ち、同じ厳密変換の全関手正方形を構成する。
方針：既存の上げ下げと nerve の全前後合成を、同じ射の型付き等式で照合する。
規約：指定同値の逆を変更しない。使われ方：元の指定入力比較の自然性。
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
lemma dgModuleResolutionChangeIdentity_lifted_source_nerve_heq :
    HEq (functorHomPostcomp (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R
      E) E F (DGFunctor.id (RightModule R E)))) (dgNerve.map ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E))) (G := G.comp (DGFunctor.id (RightModule R
      E))) a hs hq ha).comp (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionSourceLift R
          (RightModule R E) E (DGFunctor.id (RightModule R E)))) (dgStrictNatTransNerveHom R
            (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R E))))
              (DGModuleFunctorResolutionObject R (RightModule R E) E (DGFunctor.id (A := R)
                (RightModule R E))) (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a
                  hs hq ha)))
      (functorHomPrecomp (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
        (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
          (dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id (RightModule R
            E))))) (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v, max (u + 1) v}
              C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
                (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))) := by
  have hs₀ := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeIdentity_left_source R C E F)
  have ks₀ := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeIdentity_right_source R C E F G a hs hq ha)
  simp only [dgNerve.map_comp] at hs₀ ks₀
  have hud := congrArg (fun L => dgNerve.map L)
    (dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R C)
  simp only [dgNerve.map_comp, dgNerve.map_id] at hud
  have hS : (dgNerve.map (dgModuleFunctorResolutionSourceLift R (RightModule R E) E
    (DGFunctor.id (RightModule R E)))) = (dgNerve.map (dgModuleFunctorResolutionSource R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))) ≫ (dgNerve.map
        (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [dgModuleFunctorResolutionSourceLift, dgNerve.map_comp]
  have hQ : (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id
    (RightModule R E))))) = (dgNerve.map (dgModuleFunctorResolutionSource R C E (F.comp
      (DGFunctor.id (RightModule R E))))) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v,
        max (u + 1) v} R C)) := by
    simp only [dgModuleFunctorResolutionSourceLift, dgNerve.map_comp]
  have hf : (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) = (dgNerve.map
    (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (dgNerve.map F) ≫
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [dgModuleResolutionLiftedInputFunctor, dgNerve.map_comp]
  have hg : (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) = (dgNerve.map
    (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (dgNerve.map G) ≫
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [dgModuleResolutionLiftedInputFunctor, dgNerve.map_comp]
  have hh := functorHom_lifted_square_heq (dgNerve.map (dgModuleResolutionPrecompFunctor R C
    (RightModule R E) E F (DGFunctor.id (RightModule R E)))) (dgNerve.map
      ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E))) (G := G.comp (DGFunctor.id (RightModule R
      E))) a hs hq ha).comp (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionSource R C E
          (F.comp (DGFunctor.id (RightModule R E))))) (dgNerve.map
            (dgModuleFunctorResolutionSource R (RightModule R E) E (DGFunctor.id (RightModule R
              E))))
    (dgNerve.map F) (dgNerve.map G) (dgStrictNatTransNerveHom R C (RightModule R E)
      (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))
        (dgStrictNatTransNerveHom R (DGModuleFunctorResolutionObject R C E (F.comp
          (DGFunctor.id (RightModule R E)))) (DGModuleFunctorResolutionObject R (RightModule R
            E) E (DGFunctor.id (A := R) (RightModule R E)))
              (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)) hs₀ ks₀
    (dgModuleResolutionChangeIdentity_source_nerve_heq R C E F G a hs hq ha)
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) (dgNerve.map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) (dgNerve.map
        (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) hud
  have hL := functorHomPostcomp_heq_of_target_eq (dgStrictNatTransNerveHom R
    (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R E))))
      (DGModuleFunctorResolutionObject R (RightModule R E) E (DGFunctor.id (A := R)
        (RightModule R E))) (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq
          ha)) hS
  have hR := functorHom_precomp_heq (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v,
    max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
      (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
    (functorHomPrecomp ((dgNerve.map F) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max
      (u + 1) v} R (RightModule R E)))) ((dgNerve.map G) ≫ (dgNerve.map (dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E)))) (dgNerve.map
          (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C))
      (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
          (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))))
    hf hg (dgModuleResolutionChangeIdentity_lifted_original_nerve_heq R C E F G a ha)
      (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id
        (RightModule R E)))))
  have hR' := functorHomPrecomp_heq_of_source_eq
    (functorHomPrecomp ((dgNerve.map F) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max
      (u + 1) v} R (RightModule R E)))) ((dgNerve.map G) ≫ (dgNerve.map (dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E)))) (dgNerve.map
          (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C))
      (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
          (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))) hQ
  exact hL.trans (hh.trans (hR.trans hR').symm)
end SerrePositivity.InfinityCategories
