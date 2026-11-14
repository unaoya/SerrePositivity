module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamSubstitutionChainRule
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedDerivation
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
## 概要
完備分冪係数に対する多項式代入と、偏微分の連鎖律を整える。

## 方針
未完備の代入を完備化し、完備化の単位の像で偏微分の等式を照合する。

## 規約
素数p、可換環kの分冪構造、p進完備性とp乗法の単射性を固定する。

## 使われ方
完備分冪係数の代入とde Rham微分の両立のために用いる。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped BigOperators

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q') (n : ℕ)

local notation "S" => pdRaw k Q.n n
local notation "T" => pdRaw k Q'.n n
local notation "Ŝ" => pdTerm p k Q.n n
local notation "T̂" => pdTerm p k Q'.n n
local notation "uS" => principalCompletionRingCatUnit p (CommRingCat.of S)
local notation "uT" => principalCompletionRingCatUnit p (CommRingCat.of T)
local notation "φ" => substitute p γ hk hr f n

private def substituteRing : CommRingCat.of S ⟶ CommRingCat.of T :=
  CommRingCat.ofHom (φ).toRingHom

/-- 完備分冪係数の多項式代入。 -/
def substituteCompleted : Ŝ →ₐ[k] T̂ :=
  ⟨(ringCatMap p (substituteRing p γ hk hr f n)).hom, fun c => by
    change ringCatMap p (substituteRing p γ hk hr f n) (uS (algebraMap k S c)) =
      uT (algebraMap k T c)
    exact (ConcreteCategory.congr_hom
      (ringCatMap_comp_unit p (substituteRing p γ hk hr f n)) _).trans
      (congrArg (fun y : T => uT y) ((φ).commutes c))⟩

theorem substituteCompleted_unit (x : S) :
    substituteCompleted p γ hk hr f n (uS x) = uT (φ x) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p (substituteRing p γ hk hr f n)) x

/-- 完備化された多項式代入と偏微分の連鎖律。 -/
theorem substituteCompleted_partial (b : pdCoordinates Q'.n n) (x : Ŝ) :
    pdCompletedPartial p k Q'.n n b (substituteCompleted p γ hk hr f n x) =
      ∑ a : pdCoordinates Q.n n, uT (jacobian f n b a) *
        substituteCompleted p γ hk hr f n (pdCompletedPartial p k Q.n n a x) := by
  let e := substituteCompleted p γ hk hr f n
  let L := (pdCompletedPartial p k Q'.n n b).comp e.toLinearMap
  let R : Ŝ →ₗ[k] T̂ := ∑ a : pdCoordinates Q.n n,
    (LinearMap.mul k T̂ (uT (jacobian f n b a))).comp
      (e.toLinearMap.comp (pdCompletedPartial p k Q.n n a))
  have h : L = R := by
    apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p)
    intro y
    change L (uS y) = R (uS y)
    have hu (y : S) : e (uS y) = uT (φ y) :=
      substituteCompleted_unit p γ hk hr f n y
    have hL : L (uS y) = uT (pdRawPartial k Q'.n n b (φ y)) := by
      change pdCompletedPartial p k Q'.n n b (e (uS y)) = _
      rw [hu]
      exact principalCompletionLinearMap_unit k p (pdRawPartial k Q'.n n b) _
    rw [hL, substitute_partial, map_sum]
    simp only [R, LinearMap.sum_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    apply Finset.sum_congr rfl
    intro a _
    change uT (jacobian f n b a * φ (pdRawPartial k Q.n n a y)) =
      uT (jacobian f n b a) * e (pdCompletedPartial p k Q.n n a (uS y))
    rw [principalCompletionLinearMap_unit, hu, map_mul]
  change L x = _
  rw [DFunLike.congr_fun h x]
  simp only [R, LinearMap.comp_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rfl

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
