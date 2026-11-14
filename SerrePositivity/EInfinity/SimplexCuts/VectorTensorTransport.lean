module

public import SerrePositivity.EInfinity.SimplexCuts.TensorFirstSwap
public import SerrePositivity.EInfinity.IntervalCuts.TensorDegreeTransport

/-!
# 同じ斉次テンソルを指定した整数次数で読む法則

Berger–Fresse §2.2.4–6、M14 L11 の証明分割。
次数と元を対にした族は、元の degreeSum・tensorValue の入力の記法だけである。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (K : Complex A)

abbrev vectorDegree (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) : ℕ :=
  degreeSum n (fun i => (f i).1)

abbrev vectorTensor (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    (power K n).X (-(vectorDegree K n f : ℤ)) :=
  tensorValue K n (fun i => (f i).1) (fun i => (f i).2)

/-- 元の純粋テンソルの終域だけを等しい次数へ移す記法（BF §2.2.6）。 -/
def vectorTensorAt (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(vectorDegree K n f : ℤ) = t) : (power K n).X t :=
  (eqToHom (congrArg (fun z : ℤ => (power K n).X z) h)).hom (vectorTensor K n f)

/-- C325：同じ次数の和は因子の置換で不変（BF §2.2.4）。 -/
lemma vectorDegree_permutation (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (σ : Equiv.Perm (Fin n)) : vectorDegree K n (f ∘ σ) = vectorDegree K n f := by
  simp only [vectorDegree, degreeSum_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp σ (fun i => (f i).1)

/-- C333：先頭を挿入した族の、同じ元の次数和。 -/
lemma vectorDegree_cons (n : ℕ) (a : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorDegree K (n + 1) (Fin.cons a f) = a.1 + vectorDegree K n f := rfl

/-- C326：元の全次数での移送は恒等（BF §2.2.6）。 -/
@[simp] lemma vectorTensorAt_refl (n : ℕ) (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorTensorAt K n f (-(vectorDegree K n f : ℤ)) rfl = vectorTensor K n f := rfl

/-- C327：同じ斉次包含の、指定した三つの次数による再帰式（BF §2.2.6）。 -/
lemma vectorTensorAt_succ (n : ℕ) (f : Fin (n + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (i j t : ℤ) (hi : -((f 0).1 : ℤ) = i)
    (hj : -(vectorDegree K n (fun k => f k.succ) : ℤ) = j) (ht : i + j = t) :
    vectorTensorAt K (n + 1) f t (by
      simp only [vectorDegree] at hj
      simp only [vectorDegree, degreeSum, Nat.cast_add]; omega) =
      ιTensorObj K (power K n) i j t ht
        ((eqToHom (congrArg K.X hi)).hom (f 0).2 ⊗ₜ[A]
          vectorTensorAt K n (fun k => f k.succ) j hj) := by
  unfold vectorTensorAt
  dsimp only [vectorTensor]
  rw [tensorValue]
  exact IntervalCuts.tensorInclusion_transport A K (power K n) _ _ _ i j t _ ht hi hj
    (by
      simp only [vectorDegree] at hj
      simp only [vectorDegree, degreeSum, Nat.cast_add]; omega) _ _

/-- C328：同じ指定次数のテンソルの先頭挿入の評価（BF §2.2.6）。 -/
lemma vectorTensorAt_cons (n : ℕ) (a : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(a.1 : ℤ) + -(vectorDegree K n f : ℤ) = t) :
    vectorTensorAt K (n + 1) (Fin.cons a f) t
      (by simp only [vectorDegree_cons, Nat.cast_add]; omega) =
      ιTensorObj K (power K n) (-(a.1 : ℤ)) (-(vectorDegree K n f : ℤ)) t h
        (a.2 ⊗ₜ[A] vectorTensor K n f) := by
  have h' := vectorTensorAt_succ K n (Fin.cons a f) (-(a.1 : ℤ))
    (-(vectorDegree K n f : ℤ)) t rfl rfl h
  simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply,
    vectorTensorAt_refl] using! h'

/-- C329：同じ指定次数のテンソルの先頭二因子の挿入の評価（BF §2.2.6）。 -/
lemma vectorTensorAt_cons_cons (n : ℕ) (a b : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(a.1 : ℤ) + (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) = t) :
    vectorTensorAt K (n + 2) (Fin.cons a (Fin.cons b f)) t
      (by simp only [vectorDegree_cons, Nat.cast_add]; omega) =
      ιTensorObj K (K ⊗ power K n) (-(a.1 : ℤ))
        (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) t h
        (a.2 ⊗ₜ[A] ιTensorObj K (power K n) (-(b.1 : ℤ)) (-(vectorDegree K n f : ℤ))
          (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) rfl (b.2 ⊗ₜ[A] vectorTensor K n f)) := by
  rw [vectorTensorAt_succ K (n + 1) _ (-(a.1 : ℤ))
    (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) t rfl
    (by change -((b.1 + vectorDegree K n f : ℕ) : ℤ) = _; omega) h]
  simp only [Fin.cons_succ, eqToHom_refl]
  rw [vectorTensorAt_cons K n b f _ rfl]
  rfl

/-- C330：同じ斉次テンソルの先頭交換の実際の Koszul 公式（BF §2.2.4）。 -/
lemma swapFirstIso_vectorTensorAt (n : ℕ) (a b : Σ d : ℕ, K.X (-(d : ℤ)))
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (h : -(a.1 : ℤ) + (-(b.1 : ℤ) + -(vectorDegree K n f : ℤ)) = t) :
    (swapFirstIso K n).hom.f t
      (vectorTensorAt K (n + 2) (Fin.cons a (Fin.cons b f)) t
        (by simp only [vectorDegree_cons, Nat.cast_add]; omega)) =
      ((-(a.1 : ℤ)) * (-(b.1 : ℤ))).negOnePow •
        vectorTensorAt K (n + 2) (Fin.cons b (Fin.cons a f)) t
          (by simp only [vectorDegree_cons, Nat.cast_add]; omega) := by
  rw [vectorTensorAt_cons_cons K n a b f t h,
    vectorTensorAt_cons_cons K n b a f t (by omega)]
  exact swapFirstIso_apply K n _ _ _ t h a.2 b.2 (vectorTensor K n f)

/-- C344：同じ因子の族は、指定した同じ全次数でも同じテンソル（BF §2.2.6）。 -/
lemma vectorTensorAt_congr (n : ℕ) (f g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (hf : -(vectorDegree K n f : ℤ) = t) (hg : -(vectorDegree K n g : ℤ) = t)
    (hfg : f = g) : vectorTensorAt K n f t hf = vectorTensorAt K n g t hg := by
  subst g
  rfl

end SerrePositivity.EInfinity.SimplexCuts
