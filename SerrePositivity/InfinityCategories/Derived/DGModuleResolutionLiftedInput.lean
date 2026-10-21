module
public import
  SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeIdentityNerveProjection
public import SerrePositivity.InfinityCategories.Derived.FunctorHomLiftedSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompInfinity
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
def dgModuleResolutionLiftedInputFunctor :
    DGFunctor R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (DGUniverseLift.{max (u + 1)
      v, max (u + 1) v} (RightModule R E)) :=
  (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C).comp (F.comp (dgUniverseLiftUp.{u,
    max (u + 1) v, max (u + 1) v} R (RightModule R E)))
def dgModuleResolutionChangeIdentityLiftedNatTrans : StrictNatTrans
  (dgModuleResolutionLiftedInputFunctor R C E F) (dgModuleResolutionLiftedInputFunctor R C E G) :=
  dgStrictNatTransPrecomp (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)
    (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)))
lemma dgModuleResolutionChangeIdentity_lifted_original_nerve_heq :
    HEq (dgStrictNatTransNerveHom R (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
        (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
      (functorHomPrecomp ((dgNerve.map F) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v,
        max (u + 1) v} R (RightModule R E)))) ((dgNerve.map G) ≫ (dgNerve.map
          (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))))
            (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C))
        (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u,
          max (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
            (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a
              ha)))) := by
  have hp := dgStrictNatTransNerveHom_postcomp_heq
    (R := R) (C := C) (D := (RightModule R E)) (E := (DGUniverseLift.{max (u + 1) v, max (u +
      1) v} (RightModule R E))) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a
        ha) (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))
  have ht := dgStrictNatTransNerveHom_precomp_heq
    (R := R) (B := (DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)) (C := C) (D :=
      (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E)))
        (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)
    (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)))
  have he := functorHom_precomp_heq
    (dgStrictNatTransNerveHom R C (DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
      E)) (dgStrictNatTransPostcomp (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G
        a ha) (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))))
    (functorHomPostcomp (dgNerve.map F) (dgNerve.map G) (dgNerve.map (dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R (RightModule R E))) (dgStrictNatTransNerveHom R C
        (RightModule R E) (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))
    (dgNerve.map_comp F (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R
      E))) (dgNerve.map_comp G (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
        (RightModule R E))) hp (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1)
          v} R C))
  exact ht.trans he
end SerrePositivity.InfinityCategories
