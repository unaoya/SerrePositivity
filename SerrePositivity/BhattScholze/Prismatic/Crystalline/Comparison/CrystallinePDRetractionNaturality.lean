module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystallineMaps
public import SerrePositivity.BhattScholze.Delta.Division.HomExt
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDDeltaFrobeniusEvaluation
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase

/-!
# 小さい結晶模型への射の余単体自然性

## 概要
結晶の δ 除算模型から小さい分冪模型への評価を、余単体的な基底上の代数射にまとめる。

## 方針
分冪包の改名が δ 構造を保つことと、完備 p 除算環からの射の一意性を使う。

## 規約
評価の向きは結晶の δ 除算模型から小さい模型へ取る。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の結晶の橋の擬同型を小さい模型に移す。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "k" => crystallineBase p
local notation "Z" => crystallineBasePrism p
local notation "γ" => residuePdStructure p (crystallineBase_regular p) (local_base p)
local notation "Jp" => Ideal.span {(p : k)}
local notation "hp" => base_prime p
local notation "Q" => polynomial p r
local notation "hkern" => PDPolynomialFunctor.base_ker (J := Jp) Q
local notation "frame" => PDPolynomialFunctor.frame (J := Jp) Q
local notation "E" n => envelope p r n
local notation "Qp" n => pdEnvelopeCrystalline (OrientedPrism.deltaStructure Z) γ (E n)
  (regular p r n) (local_base p) (frobenius_base p)
local notation "D" n => completedFreeDeltaStructure Z (AffineIndex r n)
local notation "b" n => completedFreeDeltaBase Z (AffineIndex r n)

private theorem evaluate_delta (n : ℕ) :
    (classicalDeltaDivisionStructure (D n) (p : completedFreeDelta Z (AffineIndex r n))
      (crystallinePDDifference p r ⦋n⦌)).IsDeltaHom (Qp n).deltaStructure (evaluate.{u} p r n) := by
  unfold evaluate crystallinePDDifference
  have h := pdFrobeniusDivisionEvaluation_isDeltaHom Z r n γ (E n) (regular p r n)
    (local_base p) (frobenius_base p) (crystallineBase_generator p) (difference_mem p r n)
  unfold pdFrobeniusDifference at h
  exact h

private theorem evaluate_base (n : ℕ) (c : k) :
    evaluate.{u} p r n (pdDeltaUnit.{u} p r ⦋n⦌ ((b n) c)) = algebraMap k (E n).carrier c := by
  unfold evaluate pdDeltaUnit crystallinePDDifference
  have h := RingHom.congr_fun (pdFrobeniusDivisionEvaluation_base Z r n γ (E n)
    (regular p r n) (local_base p) (frobenius_base p) (crystallineBase_generator p)
    (difference_mem p r n)) c
  unfold pdFrobeniusDifference at h
  exact h

variable {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)

private abbrev smallMap := envelopeMap.{u} p r θ

private theorem smallMap_delta :
    (Qp m).deltaStructure.IsDeltaHom (Qp n).deltaStructure (smallMap.{u} p r θ).toRingHom := by
  apply pdEnvelopeCrystalline_isDeltaHom (Z).deltaStructure γ (E m) (E n)
    (regular p r m) (regular p r n) (local_base p) (frobenius_base p)
    (smallMap.{u} p r θ) (envelopeMap_dp.{u} p r θ)
    (fun ji => (ji.1, θ.toOrderHom ji.2))
  rintro ⟨j, i⟩
  exact envelopeMap_variable.{u} p r θ j i

private theorem evaluate_natural :
    (smallMap.{u} p r θ).toRingHom.comp (evaluate.{u} p r m) =
      (evaluate.{u} p r n).comp (pdDeltaMap.{u} p r θ) := by
  let f := (smallMap.{u} p r θ).toRingHom.comp (evaluate.{u} p r m)
  let g := (evaluate.{u} p r n).comp (pdDeltaMap.{u} p r θ)
  have hf := (smallMap_delta.{u} p r θ).comp (evaluate_delta.{u} p r m)
  have hg := (evaluate_delta.{u} p r n).comp (pdDeltaMap_spec p r θ).1
  let := (E n).isEnvelope.complete
  apply classicalPDivisionHom_ext (D m) (Qp n).deltaStructure
    (crystallinePDDifference p r ⦋m⦌) (regular p r n) f g hf hg
  have hθ (x : completedFreeDelta Z (AffineIndex r m)) :
      pdDeltaMap.{u} p r θ (pdDeltaUnit.{u} p r ⦋m⦌ x) =
        pdDeltaUnit.{u} p r ⦋n⦌ (crystallineCechSourceMap p r θ x) :=
    RingHom.congr_fun (pdDeltaMap_spec p r θ).2 x
  have hθb (c : k) : crystallineCechSourceMap p r θ ((b m) c) = (b n) c :=
    RingHom.congr_fun (crystallineCechSourceMap_spec p r θ).2.1 c
  have hθv (j : Fin r) (i : Fin (m + 1)) :
      crystallineCechSourceMap p r θ (affineVariable Z r m j i) =
        affineVariable Z r n j (θ.toOrderHom i) := by
    simpa only [affineVariable_eq, crystallineCechIndexMap] using
      (crystallineCechSourceMap_spec p r θ).2.2 ⟨(j, i)⟩
  apply completedFreeDeltaHom_ext Z (AffineIndex r m) (Qp n).deltaStructure
    (algebraMap k (E n).carrier)
    (pdEnvelopeCrystalline_base (Z).deltaStructure γ (E n)
      (regular p r n) (local_base p) (frobenius_base p)) (Qp n).complete_p
      (by rw [crystallineBase_generator, map_natCast]; exact (Qp n).complete_p)
    (hf.comp (pdDeltaUnit_isDeltaHom p r ⦋m⦌)) (hg.comp (pdDeltaUnit_isDeltaHom p r ⦋m⦌))
  · apply RingHom.ext
    intro c
    change smallMap.{u} p r θ (evaluate.{u} p r m (pdDeltaUnit.{u} p r ⦋m⦌ ((b m) c))) = _
    rw [evaluate_base]
    exact (smallMap.{u} p r θ).commutes c
  · apply RingHom.ext
    intro c
    change evaluate.{u} p r n (pdDeltaMap.{u} p r θ (pdDeltaUnit.{u} p r ⦋m⦌ ((b m) c))) = _
    rw [hθ, hθb]
    exact evaluate_base.{u} p r n c
  · rintro ⟨⟨j, i⟩⟩
    change smallMap.{u} p r θ
      (evaluate.{u} p r m (pdDeltaUnit.{u} p r ⦋m⦌ (affineVariable Z r m j i))) =
      evaluate.{u} p r n (pdDeltaMap.{u} p r θ (pdDeltaUnit.{u} p r ⦋m⦌ (affineVariable Z r m j i)))
    rw [evaluate_variable, hθ, hθv, evaluate_variable]
    exact envelopeMap_variable.{u} p r θ (ULift.up j) i

private theorem retractAt_natural :
    ((pdModel p (crystallineBase.{u} p) r).map θ).right.hom.comp (retractAt.{u} p r m) =
      (retractAt.{u} p r n).comp ((pdDeltaModel.{u} p r).map θ).right.hom := by
  have hterm (y : pdTerm p (crystallineBase.{u} p) r m) :
      termEquiv.{u} p r n (((pdModel p (crystallineBase.{u} p) r).map θ).right.hom y) =
        smallMap.{u} p r θ (termEquiv.{u} p r m y) :=
    envelopeMap_termEquiv.{u} p r θ y
  apply RingHom.ext
  intro x
  apply (termEquiv.{u} p r n).injective
  change termEquiv.{u} p r n (((pdModel p (crystallineBase.{u} p) r).map θ).right.hom
      ((termEquiv.{u} p r m).symm (evaluate.{u} p r m x))) =
    termEquiv.{u} p r n ((termEquiv.{u} p r n).symm
      (evaluate.{u} p r n (pdDeltaMap.{u} p r θ x)))
  rw [hterm, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact RingHom.congr_fun (evaluate_natural.{u} p r θ) x

/-- 結晶の δ 除算模型から小さい分冪模型への厳密な余単体射。 -/
def retraction : pdDeltaModel.{u} p r ⟶ pdModel p (crystallineBase.{u} p) r where
  app n := by
    obtain ⟨n⟩ := n
    refine Under.homMk (CommRingCat.ofHom
      (R := (pdDeltaRings.{u} p r).obj ⦋n⦌)
      (S := pdTerm p (crystallineBase.{u} p) r n) (retractAt.{u} p r n)) ?_
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change (termEquiv.{u} p r n).symm
      (evaluate.{u} p r n (pdDeltaUnit.{u} p r ⦋n⦌ ((b n) c))) = _
    rw [evaluate_base]
    exact (termEquiv.{u} p r n).symm.commutes c
  naturality {m n} θ := by
    obtain ⟨m⟩ := m
    obtain ⟨n⟩ := n
    apply Under.UnderMorphism.ext
    exact CommRingCat.hom_ext (retractAt_natural.{u} p r θ).symm

end SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction
