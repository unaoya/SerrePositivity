module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander

/-!
# 有限枠と大きい prismatic 枠の剰余構造射

## 概要
有限枠から大きい枠への射は、完備多項式環からの剰余の構造射を保つ。

## 方針
各枠の変数と係数で確認し、完備多項式環の普遍性を適用する。

## 規約
剰余は向き付き prism のイデアルによる商。

## 使われ方
BS 著者版 Remark 4.19 の枠の比較で、二つの持ち上げが剰余で一致することの確認。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {Q : Poly (A ⧸ P.ideal)} {n : ℕ} {κ : Cardinal.{u}}

local notation "C" => (A ⧸ P.ideal)

namespace BigCechTerm

variable (Y : BigCechTerm P Q n)

/-- 大きい枠の剰余への標準射は基底の剰余写像を延長する。 -/
theorem residueSection_comp :
    Y.residueSection.comp (algebraMap C (polyCompletion P Q.n)) = Y.base.quotientMap := by
  have he : Y.residueSection.comp (bigCechEval Q n) = Y.unitMod :=
    RingHom.liftOfSurjective_comp _ _ _
  apply RingHom.ext
  intro c
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h := RingHom.congr_fun he (MvPolynomial.C a)
  change Y.residueSection (bigCechEval Q n (MvPolynomial.C a)) =
    Ideal.Quotient.mk Y.prism.ideal (Y.unit (bigCechInitial P Q n (MvPolynomial.C a))) at h
  rw [bigCechEval, MvPolynomial.eval₂Hom_C, bigCechInitial_C] at h
  change Y.residueSection (algebraMap C (polyCompletion P Q.n) (Ideal.Quotient.mk P.ideal a)) =
    Y.base.quotientMap (Ideal.Quotient.mk P.ideal a)
  rw [OrientedPrism.Hom.quotientMap_mk]
  exact h

end BigCechTerm

variable (X : AffineEnvelopeTerm P Q.n n κ) (Y : BigCechTerm P Q n)

/-- 有限枠から大きい枠への比較を prism の射として読む。 -/
def affineToBigPrismHom : OrientedPrism.Hom X.X.Q Y.prism where
  toRingHom := affineToBig X Y
  map_delta := (affineToBig_spec X Y).1
  ideal_le := by
    rw [X.envelope.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change ((affineToBig X Y).comp (X.η.comp (completedFreeDeltaBase P _))) P.generator ∈
      Y.prism.ideal
    rw [X.base_eq, (affineToBig_spec X Y).2.1]
    exact Y.base.map_generator_mem

private theorem affineToBigPrismHom_base :
    (affineToBigPrismHom X Y).comp X.X.toHom = Y.base :=
  OrientedPrism.Hom.ext (affineToBig_spec X Y).2.1

/-- 有限枠から大きい枠への比較は完備多項式環からの構造射を保つ。 -/
theorem affineToBig_residueSection :
    (affineToBigPrismHom X Y).quotientMap.comp X.X.sec = Y.residueSection := by
  let f := (affineToBigPrismHom X Y).quotientMap.comp X.X.sec
  let g := Y.residueSection
  let u := prismPolynomialUnit P (Fin Q.n)
  have hc : IsModuleComplete (Y.carrier ⧸ Y.prism.ideal) (p : Y.carrier ⧸ Y.prism.ideal)
      (ModuleCat.of _ (Y.carrier ⧸ Y.prism.ideal)) :=
    isModuleComplete_principal_quotient_natCast Y.carrier p Y.prism.generator Y.prism.complete_p
  have h : f.comp u = g.comp u := by
    apply MvPolynomial.ringHom_ext'
    · rw [RingHom.comp_assoc, RingHom.comp_assoc]
      change f.comp (algebraMap C (polyCompletion P Q.n)) =
        g.comp (algebraMap C (polyCompletion P Q.n))
      unfold f g
      rw [RingHom.comp_assoc, X.X.sec_comp, Y.residueSection_comp,
        ← OrientedPrism.Hom.quotientMap_comp, affineToBigPrismHom_base]
    · intro i
      change (affineToBigPrismHom X Y).quotientMap
        (X.X.sec (u (MvPolynomial.X i))) = Y.residueSection (u (MvPolynomial.X i))
      rw [X.sec_X, OrientedPrism.Hom.quotientMap_mk]
      change Ideal.Quotient.mk Y.prism.ideal (affineToBig X Y (X.η (affineVariable P Q.n n i 0))) =
        Y.residueSection (u (MvPolynomial.X i))
      rw [(affineToBig_spec X Y).2.2]
      exact (Y.residueSection_variable (bigIndex i (0 : Fin (n + 1)))).symm
  exact (liftFromPolyCompletion_unique p (g.comp u) hc f h).trans
    (liftFromPolyCompletion_unique p (g.comp u) hc g rfl).symm

end SerrePositivity.BhattScholze.Prismatic
