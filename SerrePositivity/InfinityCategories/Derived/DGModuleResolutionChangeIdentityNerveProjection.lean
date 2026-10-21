module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransNerveHomTransport
public import
  SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityStrictProjection
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskering
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
lemma dgModuleResolutionChangeIdentity_source_nerve_heq :
    HEq (functorHomPostcomp (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)))) (dgNerve.map ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))))
      (dgNerve.map (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
      (dgStrictNatTransNerveHom R (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id
        (RightModule R E)))) (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) (dgModuleResolutionChangeIdentityStrictNatTrans
      R C E F G a hs hq ha)))
      (functorHomPrecomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map
        (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E)))))
        (dgStrictNatTransNerveHom R C (RightModule R E)
          (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) := by
  have hp := dgStrictNatTransNerveHom_postcomp_heq
    (R := R) (C := (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R
      E))))) (D := (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)))) (E := RightModule R E)
    (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)
      (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E)))
  have ht := dgStrictNatTransNerveHom_heq R (DGModuleFunctorResolutionObject R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (RightModule R E)
    (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq
      ha) (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
    (dgStrictNatTransPrecomp (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))
    (dgModuleResolutionChangeIdentity_left_source R C E F)
    (dgModuleResolutionChangeIdentity_right_source R C E F G a hs hq ha)
    (dgModuleResolutionChangeIdentity_source_strict_heq R C E F G a hs hq ha)
  have hq' := dgStrictNatTransNerveHom_precomp_heq
    (R := R) (B := (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R
      E))))) (C := C) (D := RightModule R E)
    (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)
  exact hp.symm.trans (ht.trans hq')
lemma dgModuleResolutionChangeIdentity_replacement_nerve_heq :
    HEq (functorHomPostcomp (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
    (DGFunctor.id (RightModule R E)))) (dgNerve.map ((dgModuleResolutionChangeFunctor R C E
    (F := F.comp (DGFunctor.id (RightModule R E)))
    (G := G.comp (DGFunctor.id (RightModule R E))) a hs hq ha).comp
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E G
      (DGFunctor.id (RightModule R E)))))
      (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
      (dgStrictNatTransNerveHom R (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id
        (RightModule R E)))) (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E))) (dgModuleResolutionChangeIdentityStrictNatTrans
      R C E F G a hs hq ha)))
      (𝟙 (HomotopyCategory.mk (functorVertex (dgNerve.map (dgModuleFunctorResolutionReplacement
        R C E
    (F.comp (DGFunctor.id (RightModule R E)))))))) := by
  have hp := dgStrictNatTransNerveHom_postcomp_heq
    (R := R) (C := (DGModuleFunctorResolutionObject R C E (F.comp (DGFunctor.id (RightModule R
      E))))) (D := (DGModuleFunctorResolutionObject R (RightModule R E) E
    (DGFunctor.id (A := R) (RightModule R E)))) (E := SemifreeDGModules R E)
    (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq ha)
      (dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (DGFunctor.id (RightModule R E)))
  have ht := dgStrictNatTransNerveHom_heq R (DGModuleFunctorResolutionObject R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (SemifreeDGModules R E)
    (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a hs hq
      ha) (dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
    (dgStrictNatTransId (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E)))))
    (dgModuleResolutionChangeIdentity_left_replacement R C E F)
    (dgModuleResolutionChangeIdentity_right_replacement R C E F G a hs hq ha)
    (dgModuleResolutionChangeIdentity_replacement_strict_heq R C E F G a hs hq ha)
  have hq' := dgStrictNatTransNerveHom_id R (DGModuleFunctorResolutionObject R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (SemifreeDGModules R E)
    (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E))))
  exact hp.symm.trans (ht.trans (heq_of_eq hq'))
end SerrePositivity.InfinityCategories
