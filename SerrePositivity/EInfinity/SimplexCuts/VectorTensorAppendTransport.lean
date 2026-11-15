module

public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorTransport
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-!
# 同じ斉次テンソルの連結次数と因子数の移送

Berger–Fresse §2.2.6、M14 L12a の証明分割、報告 §293。
既存のdegreeSumとvectorTensorAtを、同じ有限族のまま移送する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- 元の連結族の次数和は、前後の次数和の和（BF §2.2.6）。 -/
lemma vectorDegree_append (K : Complex A) (m n : ℕ)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorDegree K (m + n) (Fin.append f g) = vectorDegree K m f + vectorDegree K n g := by
  simp only [vectorDegree, degreeSum_eq_sum, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

/-- 因子数の等式は同じ純粋テンソルをそのまま移す（BF §2.2.6）。 -/
lemma vectorTensorAt_arity_transport (K : Complex A) {m n : ℕ} (h : m = n)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (hf : -(vectorDegree K m f : ℤ) = t) :
    (eqToHom (congrArg (power K) h)).f t (vectorTensorAt K m f t hf) =
      vectorTensorAt K n (f ∘ Fin.cast h.symm) t (by subst n; exact hf) := by
  subst n
  rfl

end SerrePositivity.EInfinity.SimplexCuts
