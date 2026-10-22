module
public import SerrePositivity.KST.SConstruction.DGHomIsoFunctorLift
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugationLaws

/-! # 対象の厳密な一致を保つ dg 関手の持ち上げ
概要：対象像が厳密に一致するとき、元の実 dg 関手そのものを回収する持ち上げを作る。
方針：等号の全 Hom 移送と閉零同型の共役を照合し、元の関手を厳密に回収する。
規約：対象等号の移送を捨てない。使われ方：標準対角の同じ comma 表示。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R]
  {E : Type w} [DGCategory R E]

/-- 元の対象等号の全 Hom 移送は、同じ実閉零同型による共役そのもの。 -/
lemma dgClosedIsoConjugation_eqToHom {x x' y y' : E} (hx : x = x') (hy : y = y') :
    eqToHom (congrArg₂ (homObject R E) hx hy) =
      enrichedClosedIsoConjugation (Complex R)
        (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) hx))
        (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) hy)) := by
  cases hx
  cases hy
  simp only [eqToHom_refl, eqToIso_refl]
  exact (enrichedClosedIsoConjugation_refl (Complex R)
    (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y)).symm

variable {P : Type t} [DGCategory R P] (F : DGFunctor R P E)

/-- 対象等号そのものによる共役は、元の実 dg 関手を厳密に保持する。 -/
lemma dgFunctorClosedConjugate_eq_of_obj_eq (a : P → E) (h : ∀ x, F.obj x = a x) :
    F = dgFunctorClosedConjugate R F a
      (fun x => eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (h x))) := by
  apply EnrichedFunctor.ext (Complex R) (F := F)
    (G := dgFunctorClosedConjugate R F a
      (fun x => eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (h x)))) h
  intro x y
  exact congrArg (fun k => F.map x y ≫ k) (dgClosedIsoConjugation_eqToHom R (h x) (h y))

variable {C : Type v} [DGCategory R C] (J : DGFunctor R C E)
  (e : ∀ x y, homObject R C x y ≅ homObject R E (J.obj x) (J.obj y))
  (he : ∀ x y, (e x y).hom = J.map x y) (b : P → C) (h : ∀ x, F.obj x = J.obj (b x))

/-- 元の対象像の厳密な一致から作る、同じ実 dg 関手の持ち上げ。 -/
def dgHomIsoFunctorLiftOfEq : DGFunctor R P C :=
  dgHomIsoFunctorLift R J e he F b
    (fun x => eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (h x)))

/-- 同じ対象等号からの持ち上げは、元の実 dg 関手そのものを厳密に回収する。 -/
lemma dgHomIsoFunctorLiftOfEq_factor : (dgHomIsoFunctorLiftOfEq R F J e he b h).comp J = F :=
  (dgHomIsoFunctorLift_factor R J e he F b
    (fun x => eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (h x)))).trans
      (dgFunctorClosedConjugate_eq_of_obj_eq R F (fun x => J.obj (b x)) h).symm

end SerrePositivity.KST.SConstruction
