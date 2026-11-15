module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveIntegerComponent
public import SerrePositivity.EInfinity.IntervalCuts.CochainDegrees

/-!
# 同じ切断成分の二つの微分の次数比較

Berger–Fresse §2.2.7、M14 L10 の証明分割。
正規化した微分公式を、元の整数複体の係数・入力の微分へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- C312：同じ次数比較を前置した正規化成分の微分公式。 -/
lemma positiveComponent_d (S : SSet.{0}) (r d q : ℕ)
    (a : (Surjection.complex A (r + 1)).X (-(d : ℤ)))
    (b : (chains A S).X (-(q : ℤ))) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ)) (-((d + q : ℕ) : ℤ) + 1)
      (positiveComponent A S r d q a b) =
    normalizedCoefficientBoundary A S r d q
      ((Surjection.complexXIso A (r + 1) d).hom a) ((chainsXIso A S q).hom b) +
    (-1 : ℤ)^d • normalizedSimplexBoundary A S r d q
      ((Surjection.complexXIso A (r + 1) d).hom a) ((chainsXIso A S q).hom b) := by
  exact congrArg (fun f => f ((Surjection.complexXIso A (r + 1) d).hom a)
    ((chainsXIso A S q).hom b)) (normalizedComponent_d A S r d q)

/-- C313：係数側の正規化した微分像は、元の整数複体の同じ微分像。 -/
lemma positiveCoefficientBoundary_succ (S : SSet.{0}) (r d q : ℕ)
    (a : (Surjection.complex A (r + 1)).X (-((d + 1 : ℕ) : ℤ)))
    (b : (chains A S).X (-(q : ℤ))) :
    normalizedCoefficientBoundary A S r (d + 1) q
      ((Surjection.complexXIso A (r + 1) (d + 1)).hom a) ((chainsXIso A S q).hom b) =
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
      (-(((d + 1) + q : ℕ) : ℤ) + 1) (by omega)
      ((Surjection.complex A (r + 1)).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) a) b := by
  rw [positiveIntegerBilinear_neg_target]
  simp only [normalizedCoefficientBoundary, LinearMap.compr₂_apply,
    LinearMap.comp_apply, LinearMap.compl₂_apply, positiveComponent]
  rw [IntervalCuts.surjection_d_neg_apply]

/-- C314：入力側の正規化した微分像は、元の整数複体の同じ微分像。 -/
lemma positiveSimplexBoundary_succ (S : SSet.{0}) (r d q : ℕ)
    (a : (Surjection.complex A (r + 1)).X (-(d : ℤ)))
    (b : (chains A S).X (-((q + 1 : ℕ) : ℤ))) :
    normalizedSimplexBoundary A S r d (q + 1)
      ((Surjection.complexXIso A (r + 1) d).hom a) ((chainsXIso A S (q + 1)).hom b) =
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
      (-((d + (q + 1) : ℕ) : ℤ) + 1) (by omega) a
      ((chains A S).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) b) := by
  rw [positiveIntegerBilinear_neg_target, chains_d_neg]
  simp only [normalizedSimplexBoundary, LinearMap.compr₂_apply,
    LinearMap.comp_apply, LinearMap.compl₂_apply, positiveComponent]
  change _ = (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z)
    (by omega : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1))).hom
    (normalizedComponent A S r d q ((Surjection.complexXIso A (r + 1) d).hom a)
      ((chainsXIso A S q).toLinearEquiv
        ((chainsXIso A S q).toLinearEquiv.symm
          ((AlexanderWhitney.chains A S).d (q + 1) q
            ((chainsXIso A S (q + 1)).hom b)))))
  rw [LinearEquiv.apply_symm_apply]

end SerrePositivity.EInfinity.SimplexCuts
