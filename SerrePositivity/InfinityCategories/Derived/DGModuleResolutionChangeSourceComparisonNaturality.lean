module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeLiftedSourceSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeInfinity
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceHomNaturality
/-!
概要：元の持ち上げ済み入力比較の指定射を、同じ実変換に自然な正方形へ同定する。
方針：両実入力射影の厳密等式と nerve 正方形を、指定余単位の自然性へ渡す。
規約：元の入力同値・指定逆・比較射を保持する。使われ方：模型変更の照合。
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
lemma dgModuleResolutionChangeIdentity_left_source_lift :
    (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))) ≫ (dgNerve.map (dgModuleFunctorResolutionSourceLift R (RightModule R
      E) E (DGFunctor.id (RightModule R E)))) = (dgNerve.map
      (dgModuleFunctorResolutionSourceLift R C E (F.comp (DGFunctor.id (RightModule R E))))) ≫
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionPrecompFunctor_sourceLift R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))
  simpa only [dgModuleResolutionLiftedInputFunctor, dgNerve.map_comp] using! h
lemma dgModuleResolutionChangeIdentity_right_source_lift :
    (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E))))) ≫ (dgNerve.map (dgModuleFunctorResolutionSourceLift R (RightModule R E) E
      (DGFunctor.id (RightModule R E)))) = (dgNerve.map (dgModuleFunctorResolutionSourceLift R
      C E (F.comp (DGFunctor.id (RightModule R E))))) ≫ (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)) := by
  have hc := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_sourceLift R C E
      (F := (F.comp (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule
        R E)))) a hs hq ha)
  simp only [dgNerve.map_comp] at hc
  calc
    _ = ((dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
      (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
      (RightModule R E))))) ≫ (dgNerve.map (dgModuleFunctorResolutionSourceLift R (RightModule
      R E) E (DGFunctor.id (RightModule R E)))) :=
      congrArg (fun t => t ≫ (dgNerve.map (dgModuleFunctorResolutionSourceLift R (RightModule R
        E) E (DGFunctor.id (RightModule R E))))) (dgNerve.map_comp
        (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id (RightModule R E))))
        (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)
        (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule
        R E))))
    _ = (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
      ((dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
      (RightModule R E)))) ≫ (dgNerve.map (dgModuleFunctorResolutionSourceLift R (RightModule R
      E) E (DGFunctor.id (RightModule R E))))) := Category.assoc _ _ _
    _ = (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
      ((dgNerve.map (dgModuleFunctorResolutionSourceLift R C E (G.comp (DGFunctor.id
      (RightModule R E))))) ≫ (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))) :=
      congrArg (fun t => (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp
        (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a
        hs hq ha)) ≫ t)
        (dgModuleResolutionChangeIdentity_left_source_lift R C E G)
    _ = ((dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
      (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E (G.comp (DGFunctor.id
      (RightModule R E)))))) ≫ (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun t => t ≫ (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))) hc
lemma dgModuleResolutionChangeIdentity_source_comparison_naturality :
    (qCatResolutionSourceComparisonIso (dgModuleFunctorResolutionSourceNerveEquivalence R C E
      (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
      (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))) (dgModuleResolutionChangeIdentity_left_source_lift R C E F)).hom ≫
      functorHomPostcomp (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F))
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))
      (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v, max
      (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
      (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha)) =
      functorHomPrecomp (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E
        F (DGFunctor.id (RightModule R E)))) (dgNerve.map ((dgModuleResolutionChangeFunctor R C
        E (F := (F.comp (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id
        (RightModule R E)))) a hs hq ha).comp (dgModuleResolutionPrecompFunctor R C
        (RightModule R E) E G (DGFunctor.id (RightModule R E)))))
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id
        (RightModule R E)))).inv (dgStrictNatTransNerveHom R (DGModuleFunctorResolutionObject R
        C E (F.comp (DGFunctor.id (RightModule R E)))) (DGModuleFunctorResolutionObject R
        (RightModule R E) E (DGFunctor.id (RightModule R E)))
        (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)) ≫
        (qCatResolutionSourceComparisonIso (dgModuleFunctorResolutionSourceNerveEquivalence R C
        E (F.comp (DGFunctor.id (RightModule R E))))
        (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
        (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))
        (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
        (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
        (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule
        R E))))) (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)).hom
        := by
  exact qCatResolutionSourceComparisonIso_hom_naturality
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule R
    E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E)))
    (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id (RightModule R
      E)))) (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E))))) (dgModuleResolutionChangeIdentity_left_source_lift R C E F)
      (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)
      (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
      (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
      (dgStrictNatTransNerveHom R (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id
      (RightModule R E)))) (DGModuleFunctorResolutionObject R (RightModule R E) E (DGFunctor.id
      (RightModule R E))) (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha))
    (dgModuleResolutionChangeIdentity_lifted_source_nerve_heq R C E F G a hs hq ha)
end SerrePositivity.InfinityCategories
