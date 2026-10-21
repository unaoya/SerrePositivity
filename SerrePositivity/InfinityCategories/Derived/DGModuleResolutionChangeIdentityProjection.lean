module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransWhisker
/-!
概要：元の二経路の厳密比較を実二射影へ送り、元の閉射と恒等成分を回収する。
方針：単位からの同じ実射の射影式を閉次数零の成分へ適用する。
規約：比較は全斉次自然性を持つ厳密変換。使われ方：模型変更比較の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
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
variable (X : DGModuleFunctorResolutionObject R C E
    (F.comp (DGFunctor.id (RightModule R E))))
lemma dgModuleResolutionChangeIdentityUnitComponent_source :
    dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha X ≫
      dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) ((dgModuleResolutionPrecompFunctor R C (RightModule R
          E) E F
    (DGFunctor.id (RightModule R E))).obj X) (((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj X) =
      ForgetEnrichment.homTo (Complex R) (a X.source) := by
  exact dgModuleIdentityResolutionPostcompHom_source R E
    (dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X)
    (G.obj X.source) (a X.source) (hs X.source) (hq X.source)
lemma dgModuleResolutionChangeIdentityUnitComponent_replacement :
    dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha X ≫
      dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
        (DGFunctor.id (RightModule R E)) ((dgModuleResolutionPrecompFunctor R C (RightModule R
          E) E F
    (DGFunctor.id (RightModule R E))).obj X) (((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj X) =
      eId (Complex R) X.replacement.val := by
  exact dgModuleIdentityResolutionPostcompHom_replacement R E
    (dgModuleResolutionPrecompObject R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)) X)
    (G.obj X.source) (a X.source) (hs X.source) (hq X.source)
lemma dgModuleResolutionChangeIdentityStrictNatTrans_app :
    (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha).app X =
      cycleFromUnit _ (dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs hq ha X) :=
  rfl
lemma dgModuleResolutionChangeIdentityStrictNatTrans_source_app :
    ((dgStrictNatTransPostcomp
      (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)
      (dgModuleFunctorResolutionSource R (RightModule R E) E
        (DGFunctor.id (RightModule R E)))).app X).val = (cycleFromUnit _
          (ForgetEnrichment.homTo (Complex R) (a X.source))).val := by
  have h := dgModuleResolutionChangeIdentityUnitComponent_source R C E F G a hs hq ha X
  have he := congrArg (fun t => (cycleFromUnit _ t).val) h
  exact (cycleFromUnit_postcomp (dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs
    hq ha X)
    (dgModuleFunctorResolutionSourceHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) ((dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X) (((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj X))).symm.trans he
lemma dgModuleResolutionChangeIdentityStrictNatTrans_replacement_app :
    ((dgStrictNatTransPostcomp
      (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)
      (dgModuleFunctorResolutionReplacement R (RightModule R E) E
        (DGFunctor.id (RightModule R E)))).app X).val = (cycleFromUnit _ (eId (Complex R)
          X.replacement.val)).val := by
  have h := dgModuleResolutionChangeIdentityUnitComponent_replacement R C E F G a hs hq ha X
  have he := congrArg (fun t => (cycleFromUnit _ t).val) h
  exact (cycleFromUnit_postcomp (dgModuleResolutionChangeIdentityUnitComponent R C E F G a hs
    hq ha X)
    (dgModuleFunctorResolutionReplacementHomMap R (RightModule R E) E
      (DGFunctor.id (RightModule R E)) ((dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E))).obj X) (((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))).obj X))).symm.trans he
end SerrePositivity.InfinityCategories
