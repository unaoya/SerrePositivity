module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionLiftedInput
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
  (ha : ∀ x y, (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
    (G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).map x y ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
lemma dgModuleResolutionChangeIdentity_lifted_source_nerve_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R
      E) E F (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R
      E))) a hs hq ha).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R
          (RightModule R E) E (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R E))))
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E (DGFunctor.id (A := R)
                (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a
                  hs hq ha)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id (RightModule R
            E))))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v}
              C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))) := by
  have hs₀ := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_left_source R C E F)
  have ks₀ := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_right_source R C E F G a hs hq ha)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hs₀ ks₀
  have hud := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R C)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] at hud
  have hS : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R (RightModule R E) E
    (DGFunctor.id (RightModule R E)))) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hQ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id
    (RightModule R E))))) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E (F.comp
      (DGFunctor.id (RightModule R E))))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v,
        max (u + 1) v} R C)) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hg : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E G)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_lifted_square_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C
    (RightModule R E) E F (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R
      E))) a hs hq ha).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E
          (F.comp (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (RightModule R E) E (DGFunctor.id (RightModule R
              E))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C (RightModule R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp
          (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R
            E) E (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)) hs₀ ks₀
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_source_nerve_heq R C E F G a hs hq ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) hud
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq_of_target_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R E))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E (DGFunctor.id (A := R)
        (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq
          ha)) hS
  have hR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v,
    max (u + 1) v} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max
      (u + 1) v} R (RightModule R E)))) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C
          (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))))
    hf hg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_lifted_original_nerve_heq R C E F G a ha)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id
        (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))
  have hR' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_heq_of_source_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max
      (u + 1) v} R (RightModule R E)))) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
        max (u + 1) v, max (u + 1) v} R (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C
          (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))) hQ
  exact hL.trans (hh.trans (hR.trans hR').symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
