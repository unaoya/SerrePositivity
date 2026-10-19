module

public import SerrePositivity.EInfinity.IntervalCuts.CoInsertionFaceEvaluation

/-!
# 内側面テンソルの有限和へのブロック余代入

概要：Berger–Fresse §2.2.6・§3.1 の内側余演算の全有限和を前後ブロックと連結する。
方針：純粋ブロック評価を内側の有限和へ分配し、各面テンソルを実際の appendIso で連結する。
規約：添字型は任意の有限型、整数係数と交換符号を保持する。
使われ方：実際の辺・頂点余演算の有限切断和を余代入へ渡す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：内側の符号付き面テンソル和は同じ係数の連結族の和へ移る（BF §3.1）。
方針：テンソル積と構成する複体射の加法性で分配し、各項を連結する。
規約：空和も含み、交換符号は和全体に掛ける。
使われ方：実際の内側辺余演算の非零切断和の評価。 -/
lemma coInsertionBlocks_face_sum_apply {ι : Type v} [Fintype ι] (C : Complex A) (s n t : ℕ)
    (θ : C ⊗ interval A ⟶ power (interval A) n)
    (c q z : ℤ) (f : Fin s → Simplex) (g : ι → Fin n → Simplex) (h : Fin t → Simplex)
    (hz : c + (-(tupleDegree s f : ℤ) + (q + -(tupleDegree t h : ℤ))) = z)
    (a : C.X c) (y : (interval A).X q) (hg : ∀ j, -(tupleDegree n (g j) : ℤ) = c + q)
    (r : ι → ℤ) (hθ : θ.f (c + q) (ιTensorObj C (interval A) c q (c + q) rfl (a ⊗ₜ[A] y)) =
      ∑ j, r j • tensorVectorAt A n (g j) (c + q) (hg j)) :
    (coInsertionBlocks (interval A) C s n t θ).f z
      (ιTensorObj C (power (interval A) s ⊗ ((interval A) ⊗ power (interval A) t))
        c (-(tupleDegree s f : ℤ) + (q + -(tupleDegree t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power (interval A) s) ((interval A) ⊗ power (interval A) t)
          (-(tupleDegree s f : ℤ)) (q + -(tupleDegree t h : ℤ))
          (-(tupleDegree s f : ℤ) + (q + -(tupleDegree t h : ℤ))) rfl
          (tensorVector A s f ⊗ₜ[A] ιTensorObj (interval A) (power (interval A) t)
            q (-(tupleDegree t h : ℤ)) (q + -(tupleDegree t h : ℤ)) rfl
            (y ⊗ₜ[A] tensorVector A t h)))) =
      (c * -(tupleDegree s f : ℤ)).negOnePow •
        ∑ j, r j • tensorVectorAt A (s + (n + t)) (Fin.append f (Fin.append (g j) h)) z
          (by rw [tupleDegree_append, tupleDegree_append]; have := hg j; omega) := by
  rw [coInsertionBlocks_apply, hθ]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hi := appendIso_tensorVectorAt A n t (g j) h (c + q) (-(tupleDegree t h : ℤ))
    (c + (q + -(tupleDegree t h : ℤ))) (hg j) rfl (by omega)
  rw [tensorVectorAt_refl] at hi
  rw [hi]
  have ho := appendIso_tensorVectorAt A s (n + t) f (Fin.append (g j) h)
    (-(tupleDegree s f : ℤ)) (c + (q + -(tupleDegree t h : ℤ))) z rfl
    (by rw [tupleDegree_append]; have := hg j; omega) (by omega)
  rw [tensorVectorAt_refl] at ho
  rw [ho]

end SerrePositivity.EInfinity.IntervalCuts
