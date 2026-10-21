module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeComparisonData
public import SerrePositivity.InfinityCategories.Derived.ResolutionOutputChangeComposition
/-!
概要：元の指定分解変更比較を、同じ実二経路の前合成比較と入力変換へ同定する。
方針：恒等入力と二段前合成則を保ち、元の指定射の共役式を回収する。
規約：同値の逆と比較を選び直さない。使われ方：元の導来射作用との照合。
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
lemma dgModuleResolutionChangeIdentity_output_right_factorization :
    (qCatResolutionOutputPrecompIso (dgModuleFunctorResolutionSourceNerveEquivalence R C E
      (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))
      (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
      (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R
      E) E (DGFunctor.id (RightModule R E))))
      (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)
      (dgModuleResolutionChangeIdentity_right_output R C E F G a hs hq ha)) =
      (qCatResolutionOutputComparisonIso (dgModuleFunctorResolutionSourceNerveEquivalence R C E
      (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E (G.comp (DGFunctor.id (RightModule
      R E)))) (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha))
      (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
      (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp
      (DGFunctor.id (RightModule R E))))) (dgModuleResolutionChangeIdentity_change_source_lift
      R C E F G a hs hq ha) (dgModuleResolutionChangeIdentity_change_output R C E F G a hs hq
      ha)) ≪≫ (qCatResolutionOutputPrecompIso (dgModuleFunctorResolutionSourceNerveEquivalence
      R C E (G.comp (DGFunctor.id (RightModule R E))))
      (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))
      (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
      (RightModule R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp
      (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))
      (dgModuleResolutionChangeIdentity_left_source_lift R C E G)
      (dgModuleResolutionChangeIdentity_left_output R C E G)) := by
  have hK : (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
    (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
    E))))) = (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
    (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
    (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
    (RightModule R E)))) := dgNerve.map_comp (dgModuleResolutionChangeFunctor R C E (F :=
    (F.comp (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E))))
    a hs hq ha) (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
    (RightModule R E)))
  have hu : ((dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
    (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
    (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
    (RightModule R E))))) ≫ (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R
    E) E (DGFunctor.id (RightModule R E))).hom =
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule
        R E)))).hom ≫ (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) :=
    (congrArg (fun J => J ≫ (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R
      E) E (DGFunctor.id (RightModule R E))).hom) hK.symm).trans
      (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)
  have huR : ((dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
    (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
    (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
    (RightModule R E))))) ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R
    E) E (DGFunctor.id (RightModule R E)))) = (dgNerve.map
    (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id (RightModule R E))))) :=
    (congrArg (fun J => J ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R
      E) E (DGFunctor.id (RightModule R E))))) hK.symm).trans
      (dgModuleResolutionChangeIdentity_right_output R C E F G a hs hq ha)
  have hm := qCatResolutionOutputPrecompIso_heq_of_maps
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule R
    E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E)))
    (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id (RightModule
      R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R E) E
      (DGFunctor.id (RightModule R E)))) (h := (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G))) (h' := (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G)))
    (H := (dgNerve.map ((dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E)))))) (H' := (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp
      (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs
      hq ha)) ≫ (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E))))) rfl hK
      (dgModuleResolutionChangeIdentity_right_source_lift R C E F G a hs hq ha)
      (dgModuleResolutionChangeIdentity_right_output R C E F G a hs hq ha) hu huR
  have hc := qCatResolutionOutputPrecompIso_comp_left_id
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule R
    E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R C E (G.comp (DGFunctor.id
    (RightModule R E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E
    (DGFunctor.id (RightModule R E)))
    (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
      (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id (RightModule R E))))
      (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) (dgNerve.map
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule R
      E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
      (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp
      (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))
    (dgModuleResolutionChangeIdentity_change_source_lift R C E F G a hs hq ha)
      (dgModuleResolutionChangeIdentity_left_source_lift R C E G) hu
      (dgModuleResolutionChangeIdentity_change_output R C E F G a hs hq ha)
      (dgModuleResolutionChangeIdentity_left_output R C E G) huR
  exact (eq_of_heq hm).trans hc
lemma dgModuleResolutionChangeIdentity_comparison_hom :
    (qCatResolutionOutputComparisonIso (dgModuleFunctorResolutionSourceNerveEquivalence R C E
      (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E (G.comp (DGFunctor.id (RightModule
      R E)))) (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha))
      (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
      (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp
      (DGFunctor.id (RightModule R E))))) (dgModuleResolutionChangeIdentity_change_source_lift
      R C E F G a hs hq ha) (dgModuleResolutionChangeIdentity_change_output R C E F G a hs hq
      ha)).hom = (qCatResolutionOutputPrecompIso
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule
      R E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E
      (DGFunctor.id (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C
      E F)) (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C
      E (F.comp (DGFunctor.id (RightModule R E))))) (dgNerve.map
      (dgModuleFunctorResolutionReplacement R (RightModule R E) E (DGFunctor.id (RightModule R
      E)))) (dgModuleResolutionChangeIdentity_left_source_lift R C E F)
      (dgModuleResolutionChangeIdentity_left_output R C E F)).hom ≫ functorHomPostcomp
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E G))
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
        (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
        (RightModule R E) E (DGFunctor.id (RightModule R E))))) (dgStrictNatTransNerveHom R
        (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1) v, max
        (u + 1) v} (RightModule R E)) (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G
        a ha)) ≫ (qCatResolutionOutputPrecompIso
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E (G.comp (DGFunctor.id
        (RightModule R E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R
        E) E (DGFunctor.id (RightModule R E))) (dgNerve.map
        (dgModuleResolutionLiftedInputFunctor R C E G)) (dgNerve.map
        (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id (RightModule
        R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp (DGFunctor.id
        (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
        R E) E (DGFunctor.id (RightModule R E))))
        (dgModuleResolutionChangeIdentity_left_source_lift R C E G)
        (dgModuleResolutionChangeIdentity_left_output R C E G)).inv := by
  have hn := dgModuleResolutionChangeIdentity_output_comparison_naturality R C E F G a hs hq ha
  have hf := congrArg Iso.hom
    (dgModuleResolutionChangeIdentity_output_right_factorization R C E F G a hs hq ha)
  have he := hn.trans hf
  apply (cancel_mono (qCatResolutionOutputPrecompIso
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E (G.comp (DGFunctor.id (RightModule R
    E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E G))
    (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G (DGFunctor.id
    (RightModule R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp
    (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R
    (RightModule R E) E (DGFunctor.id (RightModule R E))))
    (dgModuleResolutionChangeIdentity_left_source_lift R C E G)
    (dgModuleResolutionChangeIdentity_left_output R C E G)).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using! he.symm
end SerrePositivity.InfinityCategories
