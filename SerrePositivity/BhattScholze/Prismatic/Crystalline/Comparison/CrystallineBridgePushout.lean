module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridgeCoordinates
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallineAffineEnvelope
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.FrobeniusCechComparison
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallineAffineEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridgeCoordinates
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 結晶の橋は Frobenius に沿う押し出し

## 概要
結晶の橋の mod p を相対 Frobenius に沿う押し出しの左脚と同定する
（BS 著者版 Theorem 5.2 の結晶比較の mod p の部分）。

## 方針
affine envelope の p 除算表示を用い、項ごとの押し出しを余単体対象の圏へ移す。

## 規約
剰余の多項式座標で相対 Frobenius を取る。

## 使われ方
Lemma 5.4 を適用して結晶の橋のコホモロジー同型を得る。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "S" n => AffineIndex r (SimplexCategory.len n)
local notation "B" n => completedFreeDelta Z (S n)
local notation "D" n => completedFreeDeltaStructure Z (S n)
local notation "Q" => crystallineModPrimeRingMap p
local notation "q" => crystallineModPrimeProjection p

private theorem affineCompletionSquare (n : SimplexCategory) :
    IsPushout ((modPrimeMap p (crystallineCechFrobenius.{u} p r)).app n)
      ((crystallineAffineUnitModP.{u} p r).app n)
      ((modPrimeMap p (crystallinePDUnit.{u} p r)).app n)
      ((crystallineBridgeModP.{u} p r).app n) := by
  let a := crystallineAffineDifference.{u} p r n.len
  let b := crystallinePDDifference.{u} p r n
  let X := aff.{u} p r n
  let C := ClassicalDeltaDivisionCompletion (D n) (p : B n) a
  let C' := ClassicalDeltaDivisionCompletion (D n) (p : B n) b
  let η := classicalDeltaDivisionMap (D n) (p : B n) a
  let η' := classicalDeltaDivisionMap (D n) (p : B n) b
  let φ := (D n).frobeniusLift
  obtain ⟨e, he, hη⟩ := affineEnvelope_existsEquiv.{u} p r n
  let g : C →+* C' := (bridgeApp.{u} p r n).comp e.symm.toRingHom
  have hg : (classicalDeltaDivisionStructure (D n) (p : B n) a).IsDeltaHom
      (classicalDeltaDivisionStructure (D n) (p : B n) b) g := by
    have h := (bridgeApp_spec.{u} p r n).1
    rw [crystallineDivisionPrism_deltaStructure] at h
    exact h.comp he.symm
  have hgη : g.comp η = η'.comp φ := by
    have h : e.symm.toRingHom.comp η = X.η := by
      apply RingHom.ext
      intro x
      exact (congrArg e.symm (DFunLike.congr_fun hη x)).symm.trans (e.symm_apply_apply _)
    calc
      _ = (bridgeApp p r n).comp (e.symm.toRingHom.comp η) := RingHom.comp_assoc _ _ _
      _ = (bridgeApp p r n).comp X.η := congrArg (fun f => (bridgeApp p r n).comp f) h
      _ = _ := (bridgeApp_spec p r n).2
  have hs := crystallineCompletedDivision_modPrime_isPushout (D n) a (D n) b
    (crystallineAffineDivision_primeRegular p r n.len)
    (crystallineAffineFrobeniusDivision_primeRegular p r n.len)
    (frobeniusLift_isDeltaHom_of_regular (D n)
      (crystallineCompletedFreeDelta_primeRegular p (S n))) rfl hg hgη
  have hgen : (htGenerator Z hZ r n : X.X.B) = (p : X.X.B) :=
    (crystallineAffineUnit_prime.{u} p r n).symm.trans (map_natCast X.η p)
  let d : X.X.B := htGenerator Z hZ r n
  let L : Ideal X.X.B := Ideal.span {d ^ (1 : ℕ)}
  let J : Ideal C := Ideal.span {(p : C) ^ (1 : ℕ)}
  have hL : J = L.map e.toRingHom := by
    unfold L J
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : C => Ideal.span {x})
      ((map_pow e d 1).trans (congrArg (fun x : C => x ^ (1 : ℕ))
        ((congrArg e hgen).trans (map_natCast e p)))).symm
  let ε : (reducedModel (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r).obj n ≅
      crystallineModPrimeRing p (CommRingCat.of C) :=
    (Ideal.quotientEquiv L J e hL).toCommRingCatIso
  refine hs.of_iso' (Iso.refl _) (Iso.refl _) ε (Iso.refl _) ?_ ?_ ?_ ?_
  · change (𝟙 _) ≫ Q (CommRingCat.ofHom φ) = Q (CommRingCat.ofHom φ) ≫ (𝟙 _)
    simp
  · erw [Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J (η x) = Ideal.Quotient.mk J (e (X.η x))
    exact congrArg (Ideal.Quotient.mk J) (DFunLike.congr_fun hη x).symm
  · change (𝟙 _) ≫ Q (CommRingCat.ofHom η') = Q (CommRingCat.ofHom η') ≫ (𝟙 _)
    simp
  · erw [Category.comp_id]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    let J' : Ideal C' := Ideal.span {(p : C') ^ (1 : ℕ)}
    let g' : X.X.B →+* C' := bridgeApp p r n
    change Ideal.Quotient.mk J' (g (e x)) = Ideal.Quotient.mk J' (g' x)
    exact congrArg (fun y => Ideal.Quotient.mk J' (g' y)) (e.symm_apply_apply x)

private def polynomialRightLeg :
    polynomialCech (cartierBase.{u} p) (Fin r × ℕ) ⟶
      modPrimeCosimplicial p (pdDeltaRings.{u} p r) :=
  (crystallineCechResidueIso p r).inv ≫ modPrimeMap p (crystallinePDUnit p r)

private theorem polynomialSquare (n : SimplexCategory) :
    IsPushout ((deltaCoordinatesModP.{u} p r).app n)
      ((relativeFrobeniusCech p (cartierBase.{u} p) (Fin r × ℕ)).app n)
      ((crystallineBridgeModP.{u} p r).app n) ((polynomialRightLeg.{u} p r).app n) := by
  let e := (crystallineCechResidueIso.{u} p r).app n
  refine (affineCompletionSquare.{u} p r n).flip.of_iso e (Iso.refl _) e (Iso.refl _)
    ?_ (crystallineCechResidueIso_frobenius_app p r n) ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    exact (NatTrans.congr_app (crystallineCechResidueIso_hom_deltaCoordinates p r) n).symm
  · simp
  · change _ ≫ 𝟙 _ = e.hom ≫ e.inv ≫ _
    simp

/-- 結晶側の mod p は相対 Frobenius に沿う押し出しで、左脚は結晶の橋。 -/
theorem pdDelta_modP_frobeniusPushout :
    ∃ e : pushout (deltaCoordinatesModP.{u} p r)
      (relativeFrobeniusCech p (cartierBase.{u} p) (Fin r × ℕ)) ≅
        modPrimeCosimplicial p (pdDeltaRings.{u} p r),
      pushout.inl _ _ ≫ e.hom = crystallineBridgeModP p r := by
  have h := IsPushout.of_forall_isPushout_app (polynomialSquare.{u} p r)
  exact ⟨h.isoPushout.symm, h.inl_isoPushout_inv⟩

/-- 結晶の橋は mod p でコホモロジー同型（BS 著者版 Theorem 5.2 の証明の mod p）。 -/
theorem crystallineBridgeModP_isCohomologyIso :
    IsCohomologyIso (crystallineBridgeModP.{u} p r) := by
  obtain ⟨e, he⟩ := pdDelta_modP_frobeniusPushout.{u} p r
  have hi := frobeniusTwist_cech_quasiIso_infinite p (cartierBase.{u} p)
    (cartierBase_natCast p) (Fin r × ℕ) _ (deltaCoordinatesModP p r)
  intro n
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let F := (Functor.whiskeringRight SimplexCategory CommRingCat AddCommGrpCat).obj U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  change Function.Bijective (F.map (crystallineBridgeModP p r)).hom
  rw [← he, F.map_comp]
  exact (isCohomologyIso_of_isIso e.hom n).comp (hi n)

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 5.2" (partial := component) "結晶の橋の mod p のコホモロジー同型（有限変数・I＝(p)）。比較同型そのものは D68 の段 3 と結晶サイト（a1-design §11） ／ 11-10 更新。整係数の版と W(C)・J の多項式の版（Thm 6.4 で使う形）も本体 ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.crystallineBridgeModP_isCohomologyIso
