module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityProjection
/-!
概要：元の二経路の比較を両射影へ送り、同じ全厳密変換へ同定する。
方針：全 Hom 写像の等式と閉零成分を、関手の厳密等式に沿って照合する。
規約：恒等と元の入力変換を全体として回収。使われ方：指定比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex DGNerve
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
lemma dgModuleResolutionChangeIdentity_left_source :
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).comp (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))) = (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E)))).comp F := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).comp (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
    (G := (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E)))).comp F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    dgModuleFunctorResolutionSource, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionPrecompHom_source R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X Y
lemma dgModuleResolutionChangeIdentity_right_source :
    ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).comp (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))) = (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E)))).comp G := by
  apply EnrichedFunctor.ext (Complex R)
    (F := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).comp (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
    (G := (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E)))).comp G) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    dgModuleResolutionChangeFunctor, dgModuleFunctorResolutionSource,
    eqToHom_refl, Category.comp_id]
  let q := dgModuleResolutionChangeHom R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y
  let p := dgModuleResolutionPrecompHom R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y)
  let l := dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X))
      (dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y))
  have hp := dgModuleResolutionPrecompHom_source R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y)
  have hq' := dgModuleResolutionChangeHom_source R C E a hs hq ha X Y
  exact (Category.assoc q p l).trans ((congrArg (fun z => q ≫ z) hp).trans
    (((Category.assoc q
      (dgModuleFunctorResolutionSourceHomMap R C E
        (G.comp (DGFunctor.id (RightModule R E))) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y))
      (G.map X.source Y.source)).symm).trans
      (congrArg (fun z => z ≫ G.map X.source Y.source) hq')))
lemma dgModuleResolutionChangeIdentity_left_replacement :
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).comp (dgModuleFunctorResolutionReplacement R (RightModule
      R E) E
    (DGFunctor.id (RightModule R E))) = (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E)))) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).comp (dgModuleFunctorResolutionReplacement R (RightModule
      R E) E
    (DGFunctor.id (RightModule R E))))
    (G := (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E))))) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    dgModuleFunctorResolutionReplacement, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionPrecompHom_replacement R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)) X Y
lemma dgModuleResolutionChangeIdentity_right_replacement :
    ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).comp (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E
    (DGFunctor.id (RightModule R E))) = (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E)))) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
      (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)))).comp (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
    (G := (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E))))) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    dgModuleResolutionChangeFunctor, dgModuleFunctorResolutionReplacement,
    eqToHom_refl, Category.comp_id]
  let q := dgModuleResolutionChangeHom R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha X Y
  let p := dgModuleResolutionPrecompHom R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y)
  let l := dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E))
      (dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X))
      (dgModuleResolutionPrecompObject R C (RightModule R E) E G
        (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y))
  have hp := dgModuleResolutionPrecompHom_replacement R C (RightModule R E) E G
    (DGFunctor.id (RightModule R E)) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq X) (dgModuleResolutionChangeObject R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq Y)
  have hq' := dgModuleResolutionChangeHom_replacement R C E a hs hq ha X Y
  exact (Category.assoc q p l).trans ((congrArg (fun z => q ≫ z) hp).trans hq')
end SerrePositivity.InfinityCategories
