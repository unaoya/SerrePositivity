module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionSplit
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridgePushout
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDIntegral
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDIntegral
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 小さい分冪模型への結晶の橋の mod p 比較

## 概要
結晶の δ 除算模型から小さい分冪模型への評価は mod p のコホモロジー同型になる。

## 方針
整係数の切断を mod p に降ろし、既存の分冪包含のコホモロジー同型を消去する。
結晶の橋との合成にもコホモロジー同型を移す。

## 規約
比較は実際の厳密な余単体射の mod p に対して述べる。

## 使われ方
Witt の有限枠の比較を導来 p 完備化後に同定する。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

private theorem cohomologyIso_comp {X Y Z : CosimplicialObject CommRingCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsCohomologyIso f) (hg : IsCohomologyIso g) :
    IsCohomologyIso (f ≫ g) := by
  intro n
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let F := (Functor.whiskeringRight SimplexCategory CommRingCat AddCommGrpCat).obj U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  change Function.Bijective (F.map (f ≫ g)).hom
  rw [F.map_comp]
  exact (hg n).comp (hf n)

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "V" => Under.forget (CommRingCat.of (crystallineBase p))

/-- 結晶の δ 除算模型から小さい分冪模型への環の余単体射。 -/
abbrev crystallineSmallRetraction : pdDeltaRings.{u} p r ⟶ pdRings.{u} p r :=
  Functor.whiskerRight (CrystallinePDRetraction.retraction.{u} p r) V

/-- 小さい分冪模型への評価を mod p に降ろした射。 -/
abbrev crystallineSmallRetractionModP := modPrimeMap p (crystallineSmallRetraction.{u} p r)

private theorem split_modPrime :
    pdInclusionModP.{u} p r ≫ crystallineSmallRetractionModP.{u} p r =
      𝟙 (modPrimeCosimplicial p (pdRings.{u} p r)) := by
  rw [pdInclusionModP_eq_modPrime, ← modPrimeMap_comp]
  have h : Functor.whiskerRight (pdInclusion.{u} p r) V ≫
      crystallineSmallRetraction.{u} p r = 𝟙 (pdRings.{u} p r) := by
    rw [crystallineSmallRetraction, ← Functor.whiskerRight_comp,
      CrystallinePDRetraction.inclusion_comp_retraction, Functor.whiskerRight_id']
  rw [h]
  apply NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 結晶評価は mod p で全次数のコホモロジー同型を誘導する。 -/
theorem crystallineSmallRetractionModP_isCohomologyIso :
    IsCohomologyIso (crystallineSmallRetractionModP.{u} p r) := by
  intro n
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let F := (Functor.whiskeringRight SimplexCategory CommRingCat AddCommGrpCat).obj U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  have h := congrArg F.map (split_modPrime.{u} p r)
  rw [F.map_comp, F.map_id] at h
  have hi := pdInclusionModP_isCohomologyIso.{u} p r n
  change Function.Bijective (F.map (pdInclusionModP.{u} p r)).hom at hi
  change Function.Bijective (F.map (crystallineSmallRetractionModP.{u} p r)).hom
  apply (Function.Bijective.of_comp_iff _ hi).mp
  change Function.Bijective (F.map (pdInclusionModP.{u} p r) ≫
    F.map (crystallineSmallRetractionModP.{u} p r)).hom
  rw [h]
  exact Function.bijective_id

/-- mod p の結晶の橋に、小さい分冪模型への評価を続ける。 -/
def crystallineSmallBridgeModP :=
  crystallineBridgeModP.{u} p r ≫ crystallineSmallRetractionModP.{u} p r

/-- 小さい分冪模型への結晶の橋は mod p でコホモロジー同型になる。 -/
theorem crystallineSmallBridgeModP_isCohomologyIso :
    IsCohomologyIso (crystallineSmallBridgeModP.{u} p r) :=
  cohomologyIso_comp _ _ (crystallineBridgeModP_isCohomologyIso.{u} p r)
    (crystallineSmallRetractionModP_isCohomologyIso.{u} p r)

end SerrePositivity.BhattScholze.Prismatic
