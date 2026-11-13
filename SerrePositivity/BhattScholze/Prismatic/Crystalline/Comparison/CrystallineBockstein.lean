module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDIntegral
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero

/-!
# 結晶 Čech 比較と Bockstein

## 概要
結晶の橋と整係数の pd 包含を、p による Bockstein と照合する。

## 方針
項ごとの p 正則性と、正則元を保つ余単体的環射に対する自然性を使う。

## 規約
Bockstein は持ち上げた余鎖の微分を指定元で割って計算する。

## 使われ方
結晶基底の Hodge–Tate 写像の一次生成元。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.Cosimplicial

private theorem cupBockstein_base_independent
    (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n, C.obj n)
    (hd : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
    (hr : ∀ n, Function.Injective (fun x : C.obj n => d n * x))
    (k : Type u) [CommRing k] (ι κ : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C)
    (i : ℕ) (a : cohomology (quotPow C d hd 1) i) :
    cupBockstein C d hd hr k ι i a = cupBockstein C d hd hr k κ i a := by
  obtain ⟨a,rfl⟩ := cohomologyClass_surjective (quotPow C d hd 1) i a
  obtain ⟨x, y, hx, hxy⟩ := exists_regularCocycleLift C d hd i a
  let b := projectCycle C d hd (i+1) y
    (cochainDifferential_eq_zero_of_eq_mul C d hd hr i x y hxy)
  rw [cupBockstein_class C d hd hr k ι i a b x y hx rfl hxy,
    cupBockstein_class C d hd hr k κ i a b x y hx rfl hxy]

end SerrePositivity.Cosimplicial

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "k" => crystallineBase p
local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "D" => pdDeltaRings p r
local notation "C" => pdRings p r
local notation "X" => reducedModel Z hZ r

private def pdDeltaBase : (Functor.const SimplexCategory).obj (CommRingCat.of (crystallineBase.{u} p)) ⟶ D :=
  htBase Z hZ r ≫ crystallineBridge p r

private theorem pdDelta_p_regular (n : SimplexCategory) :
    Function.Injective (fun x : (pdDeltaRings.{u} p r).obj n => (p : (D).obj n) * x) := by
  have h := (targetPrism.{u} p r n).generator_regular
  rw [crystallineDivisionPrism_generator] at h
  exact h

private theorem pdRings_p_regular (n : SimplexCategory) :
    Function.Injective (fun x : (pdRings.{u} p r).obj n => (p : (C).obj n) * x) := by
  let A := pdRaw (crystallineBase.{u} p) r n.len
  have h := principalCompletionH0_smul_injective_of_regular A (p : A) (pdRaw_regular p r n.len)
  let S : Type u := pdTerm p (crystallineBase.{u} p) r n.len
  let : Algebra A S := principalCompletionAlgebra A (p : A)
  have hs (x : S) : (p : A) • x = (p : S) * x := by
    rw [Algebra.smul_def, map_natCast]
  intro x y hxy
  apply h
  let x' : S := x
  let y' : S := y
  change (p : A) • x' = (p : A) • y'
  rw [hs, hs]
  exact hxy

/-- 完備 pd Čech 模型の p による Bockstein。 -/
def pdModelBockstein (i : ℕ) :
    cohomology (modPrimeCosimplicial p (pdRings.{u} p r)) i →+
      cohomology (modPrimeCosimplicial p (pdRings.{u} p r)) (i+1) :=
  cupBockstein C (fun n => (p : (C).obj n)) (fun θ => map_natCast ((C).map θ).hom p)
    (pdRings_p_regular p r) k (pdCechBase p k r) i

/-- δ 座標つき結晶模型の p による Bockstein。 -/
def pdDeltaBockstein (i : ℕ) :
    cohomology (modPrimeCosimplicial p (pdDeltaRings.{u} p r)) i →+
      cohomology (modPrimeCosimplicial p (pdDeltaRings.{u} p r)) (i+1) :=
  cupBockstein D (fun n => (p : (D).obj n)) (fun θ => map_natCast ((D).map θ).hom p)
    (pdDelta_p_regular p r) k (pdDeltaBase p r) i

set_option backward.isDefEq.respectTransparency false in
/-- 結晶の橋は Bockstein と可換。 -/
theorem crystallineBridgeModP_bockstein (i : ℕ) (a : hodgeTateCohomology' (crystallineBasePrism.{u} p) hZ r i) :
    cohomologyMap X (modPrimeCosimplicial p D) (crystallineBridgeModP p r) (i+1)
        (bockstein Z hZ r i a) =
      pdDeltaBockstein p r i (cohomologyMap X (modPrimeCosimplicial p D) (crystallineBridgeModP p r) i a) :=
  bockstein_natural (zpCech p r) (htGenerator Z hZ r) (htGenerator_nat Z hZ r)
    (htGenerator_regular Z hZ r) k (htBase Z hZ r) D
    (fun n => (p : (D).obj n)) (fun θ => map_natCast ((D).map θ).hom p)
    (pdDelta_p_regular p r) (crystallineBridge p r) (crystallineBridge_generator p r) i a

set_option backward.isDefEq.respectTransparency false in
/-- 整係数で構成した pd 包含は Bockstein と可換。 -/
theorem pdInclusionModP_bockstein (i : ℕ) (a : cohomology (modPrimeCosimplicial p (pdRings.{u} p r)) i) :
    cohomologyMap (modPrimeCosimplicial p C) (modPrimeCosimplicial p D) (pdInclusionModP p r) (i+1)
        (pdModelBockstein p r i a) =
      pdDeltaBockstein p r i (cohomologyMap (modPrimeCosimplicial p C) (modPrimeCosimplicial p D)
        (pdInclusionModP p r) i a) := by
  let g := Functor.whiskerRight (pdInclusion p r) (Under.forget (CommRingCat.of k))
  rw [pdInclusionModP_eq_modPrime]
  have h := bockstein_natural C (fun n => (p : (C).obj n)) (fun θ => map_natCast ((C).map θ).hom p)
    (pdRings_p_regular p r) k (pdCechBase p k r) D
    (fun n => (p : (D).obj n)) (fun θ => map_natCast ((D).map θ).hom p)
    (pdDelta_p_regular p r) g (fun n => map_natCast (g.app n).hom p) i a
  refine h.trans ?_
  exact cupBockstein_base_independent D _ _ (pdDelta_p_regular p r) k _ (pdDeltaBase p r) i _

end SerrePositivity.BhattScholze.Prismatic
