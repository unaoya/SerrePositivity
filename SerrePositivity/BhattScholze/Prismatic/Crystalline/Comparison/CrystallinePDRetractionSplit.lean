module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDTermRingHomExt
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineGeneratorBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineGeneratorBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDIntegral
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermReductionLinear
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 結晶の分冪包含の切断

## 概要
小さい分冪模型を結晶の δ 除算模型に入れてから評価すると恒等射になる。

## 方針
既存の零次座標の式を余単体自然性で各頂点に移す。
p 正則な完備標的への環射の一意性を適用する。

## 規約
整係数の厳密な自然変換の等式を示す。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の小さい結晶比較の mod p の擬同型。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction

set_option backward.isDefEq.respectTransparency false
-- 二つの完備模型の構造射と分冪包の比較同型の型を照合する。

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

private theorem inclusion_copy (n : ℕ) (j : Fin r) (i : Fin (n + 1)) :
    ((pdInclusion.{u} p r).app ⦋n⦌).right
      ((pdTermCompletionUnitAlg p (crystallineBase.{u} p) r n) (copy k r ⦋n⦌ j i)) =
      pdDeltaUnit.{u} p r ⦋n⦌ (affineVariable Z r n j i) := by
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ i
  let x := (pdTermCompletionUnitAlg p (crystallineBase.{u} p) r 0) (copy k r ⦋0⦌ j 0)
  have hx : ((pdModel p (crystallineBase.{u} p) r).map θ).right x =
      (pdTermCompletionUnitAlg p (crystallineBase.{u} p) r n) (copy k r ⦋n⦌ j i) := by
    have h := ConcreteCategory.congr_hom
      (ringCatMap_comp_unit p ((pdRawModel k r).map θ).right) (copy k r ⦋0⦌ j 0)
    change ((pdModel p (crystallineBase.{u} p) r).map θ).right x = _ at h
    exact h.trans (congrArg (pdTermCompletionUnitAlg p (crystallineBase.{u} p) r n)
      (pdRawMap_copy k r θ j 0))
  have hi : ((pdInclusion.{u} p r).app ⦋0⦌).right x =
      pdDeltaUnit.{u} p r ⦋0⦌ (affineVariable Z r 0 j 0) := pdInclusion_coordinate.{u} p r j
  have hn := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right ((pdInclusion.{u} p r).naturality θ)) x
  change ((pdInclusion.{u} p r).app ⦋n⦌).right
      (((pdModel p (crystallineBase.{u} p) r).map θ).right x) =
    pdDeltaMap.{u} p r θ (((pdInclusion.{u} p r).app ⦋0⦌).right x) at hn
  rw [hx, hi] at hn
  have hθ : pdDeltaMap.{u} p r θ (pdDeltaUnit.{u} p r ⦋0⦌ (affineVariable Z r 0 j 0)) =
      pdDeltaUnit.{u} p r ⦋n⦌ (affineVariable Z r n j i) := by
    have h := RingHom.congr_fun (pdDeltaMap_spec p r θ).2 (affineVariable Z r 0 j 0)
    change pdDeltaMap.{u} p r θ (pdDeltaUnit.{u} p r ⦋0⦌ (affineVariable Z r 0 j 0)) = _ at h
    exact h.trans (congrArg (pdDeltaUnit.{u} p r ⦋n⦌)
      ((crystallineCechSourceMap_spec p r θ).2.2 ⟨(j, 0)⟩))
  exact hn.trans hθ

private theorem split_at (n : ℕ) :
    ((pdInclusion.{u} p r) ≫ retraction.{u} p r).app ⦋n⦌ =
      𝟙 ((pdModel p (crystallineBase.{u} p) r).obj ⦋n⦌) := by
  let c := ((pdInclusion.{u} p r) ≫ retraction.{u} p r).app ⦋n⦌
  let f : pdTerm p (crystallineBase.{u} p) r n →ₐ[k] pdTerm p (crystallineBase.{u} p) r n :=
    { toRingHom := c.right.hom
      commutes' := fun a => by
        have h := ConcreteCategory.congr_hom (Under.w c) a
        exact h }
  let e := termEquiv.{u} p r n
  have hl (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : (envelope.{u} p r n).carrier) := by
    simpa only [map_natCast] using (local_base p m hm).map
      (algebraMap k (envelope.{u} p r n).carrier)
  have hc := (pdEnvelopeCrystalline (Z).deltaStructure γ (envelope.{u} p r n) (regular p r n)
    (local_base p) (frobenius_base p)).complete_p
  have heq : e.toAlgHom.comp f = e.toAlgHom := by
    apply pdTermAlgHom_ext_of_primeRegular p r n (regular p r n) hl hc
    intro j i
    change e (retractAt.{u} p r n (((pdInclusion.{u} p r).app ⦋n⦌).right
      ((pdTermCompletionUnitAlg p (crystallineBase.{u} p) r n)
        (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i)))))) =
      e ((pdTermCompletionUnitAlg p (crystallineBase.{u} p) r n)
        (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i))))
    rw [PDSmallRawEnvelope.unit_X, inclusion_copy, at_variable, PDSmallRawEnvelope.unit_X]
    rfl
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply e.injective
  exact DFunLike.congr_fun heq x

/-- 小さい分冪模型の包含と結晶評価の合成は恒等射。 -/
theorem inclusion_comp_retraction :
    pdInclusion.{u} p r ≫ retraction.{u} p r =
      𝟙 (pdModel p (crystallineBase.{u} p) r) := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  exact split_at p r n

end SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction
