module
public import
  SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeSourceComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.ResolutionOutputHomNaturality
/-!
概要：元の実二経路と指定逆を保ち、入力変換に対する指定出力比較の射を計算する。
方針：持ち上げ済み入力正方形と、出力での同じ恒等射を自然性定理へ渡す。
規約：出力の射影性を追加しない。使われ方：元の分解変更同型の照合。
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
lemma dgModuleResolutionChangeIdentity_left_output :
    (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))) ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
      R E) E (DGFunctor.id (RightModule R E)))) = (dgNerve.map
      (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id (RightModule R E))))) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeIdentity_left_replacement R C E F)
  simpa only [dgNerve.map_comp] using! h
lemma dgModuleResolutionChangeIdentity_right_output :
    (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E))))) ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R E) E
      (DGFunctor.id (RightModule R E)))) = (dgNerve.map (dgModuleFunctorResolutionReplacement R
      C E (F.comp (DGFunctor.id (RightModule R E))))) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeIdentity_right_replacement R C E F G a hs hq ha)
  simpa only [dgNerve.map_comp] using! h
lemma dgModuleResolutionChangeIdentity_output_comparison_naturality :
    (qCatResolutionOutputPrecompIso (dgModuleFunctorResolutionSourceNerveEquivalence R C E
      (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
      (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp
      (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))
      (dgModuleResolutionChangeIdentity_left_source_lift R C E F)
      (dgModuleResolutionChangeIdentity_left_output R C E F)).hom ≫ functorHomPostcomp
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G))
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
        (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
        (RightModule R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R
        (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max
        (u + 1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G
        a ha)) = (qCatResolutionOutputPrecompIso
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id
        (RightModule R E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R
        E) E (DGFunctor.id (RightModule R E))) (dgNerve.map
        (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
        ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id (RightModule R
        E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
        (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule
        R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
        (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
        R E) E (DGFunctor.id (RightModule R E))))
        (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)
        (dgModuleResolutionChangeIdentity_right_output R C E F G a hs hq ha)).hom := by
  exact qCatResolutionOutputPrecompIso_hom_naturality
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule R
    E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E)))
    (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id (RightModule R
      E)))) (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
      (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R
      E) E (DGFunctor.id (RightModule R E))))
    (dgModuleResolutionChangeIdentity_left_source_lift R C E F)
      (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)
      (dgModuleResolutionChangeIdentity_left_output R C E F)
      (dgModuleResolutionChangeIdentity_right_output R C E F G a hs hq ha)
      (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
      (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
      (dgStrictNatTransNerveHom R (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id
      (RightModule R E)))) (DGModuleFunctorResolutionObject R (RightModule R E) E (DGFunctor.id
      (RightModule R E))) (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha))
    (dgModuleResolutionChangeIdentity_lifted_source_nerve_heq R C E F G a hs hq ha)
    (dgModuleResolutionChangeIdentity_replacement_nerve_heq R C E F G a hs hq ha)
end SerrePositivity.InfinityCategories
