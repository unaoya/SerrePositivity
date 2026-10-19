module

public import SerrePositivity.EInfinity.IntervalCuts.TensorFamilyBlocks
public import SerrePositivity.EInfinity.IntervalCuts.CoInsertionFaceSums

/-!
# 実際の指定位置の余代入への内側有限和の代入

概要：Berger–Fresse §2.2.6・§3.1 の tensorCoInsertionAction を元の出力族のまま評価する。
方針：入力面テンソルをブロックへ分け、既存の余代入との等式から面テンソル評価へ戻す。
規約：交換符号は元の族の prefixDegree で表す。
使われ方：二段余演算の右辺を共通の全出力族の有限和に移す。
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

attribute [local implicit_reducible] TensorPowers.power

/-- 概要：元の出力族上の余代入は前方次数の Koszul 符号付きの置換族（BF §3.1）。
方針：元の面テンソルを三ブロックへ分け、実際の余代入のブロック評価と再連結を使う。
規約：内側作用の全有限和と各整数係数を保持する。
使われ方：実際の内側辺・頂点の余演算の各項を共通出力族へ送る。 -/
lemma tensorCoInsertionAction_face_sum_apply {ι : Type v} [Fintype ι] (C : Complex A)
    (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ interval A ⟶ power (interval A) n)
    (c z : ℤ) (f : Fin (m + 1) → Simplex) (g : ι → Fin n → Simplex)
    (hz : c + (-(tupleDegree i.val (prefixFamily f i) : ℤ) +
      (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ))) = z)
    (a : C.X c) (hg : ∀ j, -(tupleDegree n (g j) : ℤ) = c + -(simplexDegree (f i) : ℤ))
    (r : ι → ℤ) (hθ : θ.f (c + -(simplexDegree (f i) : ℤ))
      (ιTensorObj C (interval A) c (-(simplexDegree (f i) : ℤ))
        (c + -(simplexDegree (f i) : ℤ)) rfl (a ⊗ₜ[A] faceVector A (f i))) =
      ∑ j, r j • tensorVectorAt A n (g j) (c + -(simplexDegree (f i) : ℤ)) (hg j)) :
    (tensorCoInsertionAction (interval A) C m n i θ).f z
      (ιTensorObj C (power (interval A) (m + 1)) c
        (-(tupleDegree i.val (prefixFamily f i) : ℤ) +
          (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ)))
        z hz (a ⊗ₜ[A] tensorVectorAt A (m + 1) f _ (by
          have := tupleDegree_family_blocks f i; omega))) =
      (c * -(prefixDegree (m + 1) f i : ℤ)).negOnePow •
        ∑ j, r j • tensorVectorAt A (m + n) (insertionFamily f (g j) i) z (by
          rw [tupleDegree_insertionFamily]; have := hg j; omega) := by
  let p := -(tupleDegree i.val (prefixFamily f i) : ℤ)
  let q := -(simplexDegree (f i) : ℤ)
  let b := -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ)
  have hf : -(tupleDegree (m + 1) f : ℤ) = p + (q + b) := by
    have := tupleDegree_family_blocks f i
    dsimp only [p, q, b]
    omega
  let x := ιTensorObj C (power (interval A) i.val ⊗
      ((interval A) ⊗ power (interval A) (m - i.val))) c (p + (q + b)) z hz
    (a ⊗ₜ[A] ιTensorObj (power (interval A) i.val)
      ((interval A) ⊗ power (interval A) (m - i.val)) p (q + b) (p + (q + b)) rfl
      (tensorVector A i.val (prefixFamily f i) ⊗ₜ[A]
        ιTensorObj (interval A) (power (interval A) (m - i.val)) q b (q + b) rfl
          (faceVector A (f i) ⊗ₜ[A] tensorVector A (m - i.val) (suffixFamily f i))))
  have H := congrArg (fun φ => φ.f z x)
    (tensorCoInsertionAction_on_blocks (interval A) C m n i θ)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
  have hinput : (C ◁ ((appendIso (interval A) i.val (m - i.val + 1)).hom ≫
      eqToHom (congrArg (power (interval A))
        (by omega : i.val + (m - i.val + 1) = m + 1)))).f z x =
      ιTensorObj C (power (interval A) (m + 1)) c (p + (q + b)) z hz
        (a ⊗ₜ[A] tensorVectorAt A (m + 1) f (p + (q + b)) hf) := by
    dsimp only [x]
    erw [SerrePositivity.DifferentialGraded.whiskerLeft_apply]
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    erw [← tensorVectorAt_family_blocks A f i (p + (q + b)) hf]
  rw [hinput] at H
  rw [H]
  dsimp only [x, p, q, b]
  erw [coInsertionBlocks_face_sum_apply A C i.val n (m - i.val) θ c _ z
    (prefixFamily f i) g (suffixFamily f i) hz a (faceVector A (f i)) hg r hθ]
  simp only [Units.smul_def, map_sum, map_zsmul, tupleDegree_prefixFamily]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [tensorVectorAt_arity_transport A
    (by omega : i.val + (n + (m - i.val)) = m + n)
    (Fin.append (prefixFamily f i) (Fin.append (g j) (suffixFamily f i))) z
    (by rw [tupleDegree_append, tupleDegree_append]; have := hg j; omega)]
  simp only [← insertionFamily_eq_blocks f (g j) i]

end SerrePositivity.EInfinity.IntervalCuts
