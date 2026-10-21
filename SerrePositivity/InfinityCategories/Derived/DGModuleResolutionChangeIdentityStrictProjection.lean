module
public import
  SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityFunctorProjection
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTrans
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
def dgModuleResolutionChangeIdentityOriginalNatTrans : StrictNatTrans F G :=
  dgModuleStrictNatTransOfHomNaturality R E a (by
    intro x y
    simpa only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map, Category.comp_id,
      moduleHomPostcompose, moduleHomPrecompose] using! ha x y)
lemma dgModuleResolutionChangeIdentity_source_strict_heq :
    HEq (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a
      hs hq ha) (dgModuleFunctorResolutionSource R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
      (dgStrictNatTransPrecomp (dgModuleFunctorResolutionSource R C E
    (F.comp (DGFunctor.id (RightModule R E))))
      (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)) := by
  apply dgStrictNatTrans_heq_of_val
  · exact dgModuleResolutionChangeIdentity_left_source R C E F
  · exact dgModuleResolutionChangeIdentity_right_source R C E F G a hs hq ha
  · intro X
    exact heq_of_eq
      (dgModuleResolutionChangeIdentityStrictNatTrans_source_app R C E F G a hs hq ha X)
lemma dgModuleResolutionChangeIdentity_replacement_strict_heq :
    HEq (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityStrictNatTrans R C E F G a
      hs hq ha) (dgModuleFunctorResolutionReplacement R (RightModule R E) E
    (DGFunctor.id (RightModule R E))))
      (dgStrictNatTransId (dgModuleFunctorResolutionReplacement R C E
    (F.comp (DGFunctor.id (RightModule R E))))) := by
  apply dgStrictNatTrans_heq_of_val
  · exact dgModuleResolutionChangeIdentity_left_replacement R C E F
  · exact dgModuleResolutionChangeIdentity_right_replacement R C E F G a hs hq ha
  · intro X
    exact heq_of_eq
      (dgModuleResolutionChangeIdentityStrictNatTrans_replacement_app R C E F G a hs hq ha X)
end SerrePositivity.InfinityCategories
