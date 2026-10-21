module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawConjugation
/-!
概要：指定済みの実出力分解の比較の射を、同じ元の nerve 作用へ照合する。
方針：全関手射の上げ下げと指定逆を保つ共役式を使う。
規約：比較の値を再選択しない。使われ方：導来 kernel の準同型比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
variable {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))
lemma dgModuleResolvedInfinity_changeIso_hom :
    (dgModuleResolvedInfinity_changeIso R C E a hs hq ha).hom =
      (dgModuleResolvedInfinity_rawFactorIso R C E F).hom ≫ (functorHomPostcomp (dgNerve.map F)
      (dgNerve.map G) (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule
      R E))) (dgStrictNatTransNerveHom R C (RightModule R E)
      (dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha))) ≫
      (dgModuleResolvedInfinity_rawFactorIso R C E G).inv :=
  eq_of_heq ((dgModuleResolvedInfinity_changeIso_hom_raw_heq R C E a hs hq ha).trans
    (dgModuleResolvedInfinity_rawFactor_conjugation_raw_heq R C E a ha))
end SerrePositivity.InfinityCategories
