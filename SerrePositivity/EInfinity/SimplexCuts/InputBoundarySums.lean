module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryTerms

/-!
# 入力境界の和と同じ切断和の交代面和

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の同じcutSumの次数移送を合成し、入力面の全添字を有限和としてまとめる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C265：同じ入力面に属する切断の和は、同じ面のcutSumへ戻る。 -/
lemma simplexBoundaryTerm_sum_cut (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (i : Fin (q + 2)) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    ∑ s : Cut (r + d) q, simplexBoundaryTerm A S w (q + 1) (i, s) x =
      -((-1 : ℤ) ^ (d + i.val)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
          (cutSum A S w (S.δ i x)) := by
  simp only [simplexBoundaryTerm, ← Finset.smul_sum]
  unfold cutSum
  have step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
      (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
    subst N
    subst P
    rfl
  rw [step]
  simp only [map_sum]

/-- C266：全入力境界項の和を、同じ入力面番号ごとのcutSumへまとめる。 -/
lemma sum_simplexBoundaryTerm_succ_by_face (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    ∑ c : SimplexBoundaryIndex r d (q + 1), simplexBoundaryTerm A S w (q + 1) c x =
      ∑ i : Fin (q + 2), -((-1 : ℤ) ^ (d + i.val)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
          (cutSum A S w (S.δ i x)) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact simplexBoundaryTerm_sum_cut A S w i x h

/-- C267：入力境界全和の符号は、係数次数のKoszul符号と入力面の交代符号。 -/
lemma sum_simplexBoundaryTerm_succ (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    ∑ c : SimplexBoundaryIndex r d (q + 1), simplexBoundaryTerm A S w (q + 1) c x =
      -((-1 : ℤ) ^ d) •
        ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutSum A S w (S.δ i x)) := by
  rw [sum_simplexBoundaryTerm_succ_by_face A S w x h]
  simp only [Finset.smul_sum, ← mul_smul, pow_add, neg_mul]

end SerrePositivity.EInfinity.SimplexCuts
