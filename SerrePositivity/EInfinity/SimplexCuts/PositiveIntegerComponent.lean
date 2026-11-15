module

public import SerrePositivity.EInfinity.SimplexCuts.NormalizedComponentDifferential

/-!
# 同じ正規化切断成分の整数次数への延長

Berger–Fresse §2.2.6–7、M14 L10 の証明分割。
元の負自然数次数の成分を等しい次数の比較で移し、正次数を零にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 元の正 arity の成分を、両入力の同じ非正整数次数で読む（BF §2.2.6）。 -/
def positiveIntegerBilinear (S : SSet.{0}) (r : ℕ) (i j t : ℤ) (h : i + j = t) :
    (Surjection.complex A (r + 1)).X i →ₗ[A] (chains A S).X j →ₗ[A]
      (power (chains A S) (r + 1)).X t :=
  if hi : i ≤ 0 then
    if hj : j ≤ 0 then
      ((((positiveComponent A S r (-i).toNat (-j).toNat).comp
        (eqToHom (congrArg (fun z : ℤ => (Surjection.complex A (r + 1)).X z)
          (by omega : i = -(((-i).toNat : ℕ) : ℤ)))).hom).compl₂
        (eqToHom (congrArg (fun z : ℤ => (chains A S).X z)
          (by omega : j = -(((-j).toNat : ℕ) : ℤ)))).hom).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z)
          (by omega : -((((-i).toNat + (-j).toNat : ℕ) : ℤ)) = t))).hom)
    else 0
  else 0

/-- C305：負自然数次数では、指定した元の正規化成分そのもの。 -/
lemma positiveIntegerBilinear_neg (S : SSet.{0}) (r d q : ℕ) :
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ)) (-((d + q : ℕ) : ℤ)) (by omega) =
      positiveComponent A S r d q := by
  cases d <;> cases q <;> rfl

/-- C309：正の係数次数では、同じ零延長の零成分。 -/
lemma positiveIntegerBilinear_eq_zero_left (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) (hi : 0 < i) :
    positiveIntegerBilinear A S r i j t h = 0 := by
  simp only [positiveIntegerBilinear, show ¬i ≤ 0 by omega, dite_false]

/-- C310：正の入力次数では、同じ零延長の零成分。 -/
lemma positiveIntegerBilinear_eq_zero_right (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) (hj : 0 < j) :
    positiveIntegerBilinear A S r i j t h = 0 := by
  unfold positiveIntegerBilinear
  split
  · simp only [show ¬j ≤ 0 by omega, dite_false]
  · rfl

/-- C311：同じ負次数の成分は、指定した和の次数へ等式移送したもの。 -/
lemma positiveIntegerBilinear_neg_target (S : SSet.{0}) (r d q : ℕ) (t : ℤ)
    (h : -(d : ℤ) + -(q : ℤ) = t) :
    positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ)) t h =
      (positiveComponent A S r d q).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z)
          (by omega : -((d + q : ℕ) : ℤ) = t))).hom := by
  have ht : t = -((d + q : ℕ) : ℤ) := by omega
  subst ht
  change positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
    (-((d + q : ℕ) : ℤ)) (by omega) = positiveComponent A S r d q
  exact positiveIntegerBilinear_neg A S r d q

end SerrePositivity.EInfinity.SimplexCuts
