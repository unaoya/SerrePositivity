module

public import SerrePositivity.EInfinity.PowerOperation.MayMixedInputNorm
public import SerrePositivity.EInfinity.PowerOperation.MayCoefficientAction

/-!
# May の同じ作用における係数と入力のノルム

May, Proposition 2.3(ii) の境界表示の補助。
実代数の同時置換の等変性により、係数のノルムを入力のノルムへ移す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k]

lemma mayInputPermutation_inv_cancel (K : Complex k) (p : ℕ)
    (σ : Equiv.Perm (Fin p)) (i : ℤ) (y : (power K p).X i) :
    (permutationAction K p σ).asIso.hom.f i
      ((permutationAction K p σ⁻¹).asIso.hom.f i y) = y := by
  have h := permutationAction_mul K p σ σ⁻¹
  rw [mul_inv_cancel, permutationAction_one] at h
  have he := congrArg (fun f => f.f i y) h
  change y = (permutationAction K p σ).asIso.hom.f i
    ((permutationAction K p σ⁻¹).asIso.hom.f i y) at he
  exact he.symm

variable (X : (operad k).Algebra) (p : ℕ) [NeZero p] (s : ℕ) (q : ℤ)

/-- 係数の群作用は、同じ入力の逆置換へ厳密に移せる。 -/
lemma mayCoefficientAction_transfer (g : MayCyclicGroup.{u} p)
    (c : (mayArityResolution p k).complex.X s)
    (y : (power X.carrier p).X (mayRepeatedDegree q p)) :
    mayHomogeneousAction X p (-(s : ℤ)) (mayRepeatedDegree q p)
      (mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ g c)) y =
    mayHomogeneousAction X p (-(s : ℤ)) (mayRepeatedDegree q p) (mayActualCoefficient p s c)
      ((permutationAction X.carrier p g.val.down⁻¹).asIso.hom.f (mayRepeatedDegree q p) y) := by
  rw [mayCoefficientAction_eq]
  have he := mayHomogeneousAction_equivariance X p g.val.down (-(s : ℤ))
    (mayRepeatedDegree q p) c
    ((permutationAction X.carrier p g.val.down⁻¹).asIso.hom.f (mayRepeatedDegree q p) y)
  rw [mayInputPermutation_inv_cancel] at he
  exact he

/-- 同じ有限巡回ノルムを、係数から入力へ厳密に移す。 -/
lemma mayCoefficientNorm_transfer
    (c : (mayArityResolution p k).complex.X s)
    (y : (power X.carrier p).X (mayRepeatedDegree q p)) :
    mayHomogeneousAction X p (-(s : ℤ)) (mayRepeatedDegree q p)
      (mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ.norm c)) y =
    mayHomogeneousAction X p (-(s : ℤ)) (mayRepeatedDegree q p) (mayActualCoefficient p s c)
      (mayInputNorm p X.carrier q y) := by
  let L := (mayHomogeneousActionLinear X p (-(s : ℤ)) (mayRepeatedDegree q p)).flip y
  let R := mayHomogeneousActionLinear X p (-(s : ℤ)) (mayRepeatedDegree q p) c
  calc
    _ = ∑ g : MayCyclicGroup.{u} p, mayHomogeneousAction X p (-(s : ℤ))
        (mayRepeatedDegree q p) (mayActualCoefficient p s
          (((mayArityResolution p k).complex.X s).ρ g c)) y := by
      change L ((∑ g : MayCyclicGroup.{u} p,
        ((mayArityResolution p k).complex.X s).ρ g) c) = ∑ g, L _
      rw [LinearMap.sum_apply, map_sum]
    _ = ∑ g : MayCyclicGroup.{u} p, R
        ((permutationAction X.carrier p g.val.down⁻¹).asIso.hom.f (mayRepeatedDegree q p) y) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact mayCoefficientAction_transfer X p s q g c y
    _ = ∑ g : MayCyclicGroup.{u} p, R
        ((permutationAction X.carrier p g.val.down).asIso.hom.f (mayRepeatedDegree q p) y) := by
      exact Equiv.sum_comp (Equiv.inv (MayCyclicGroup.{u} p))
        (fun g => R ((permutationAction X.carrier p g.val.down).asIso.hom.f
          (mayRepeatedDegree q p) y))
    _ = _ := by
      change (∑ g : MayCyclicGroup.{u} p, R _) = R (mayInputNorm p X.carrier q y)
      rw [mayInputNorm, LinearMap.sum_apply, map_sum]

end SerrePositivity.EInfinity.PowerOperation
