module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNatTransNerveHomTransport
public import
  SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionChangeIdentityStrictProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskering
/-!
概要：元の厳密二経路比較の nerve 像を、入力の同じ変換と出力の恒等へ同定する。
方針：全厳密変換の型付き比較と nerve の前後合成を接続する。
規約：頂点だけの一致で代用しない。使われ方：指定分解比較の自然性。
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
lemma dgModuleResolutionChangeIdentity_source_nerve_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) a hs hq ha).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id
        (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans
      R C E F G a hs hq ha)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C (RightModule R E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq
    (R := R) (C := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R
      E))))) (D := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))) (E := _root_.SerrePositivity.DifferentialGraded.RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq
      ha) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_left_source R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_right_source R C E F G a hs hq ha)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_source_strict_heq R C E F G a hs hq ha)
  have hq' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq
    (R := R) (B := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R
      E))))) (C := C) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)
  exact hp.symm.trans (ht.trans hq')
lemma dgModuleResolutionChangeIdentity_replacement_nerve_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeFunctor R C E
    (F := F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
    (G := G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) a hs hq ha).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id
        (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans
      R C E F G a hs hq ha)))
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement
        R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))))) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq
    (R := R) (C := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R
      E))))) (D := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)))) (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq
      ha) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransId (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_left_replacement R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_right_replacement R C E F G a hs hq ha)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_replacement_strict_heq R C E F G a hs hq ha)
  have hq' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_id R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E
    (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
  exact hp.symm.trans (ht.trans (heq_of_eq hq'))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
