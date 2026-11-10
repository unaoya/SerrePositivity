module

public import SerrePositivity.AlgebraicGeometry.DeterminantalCenter
public import Mathlib.LinearAlgebra.Pi

/-!
概要：自由標的に階数一の直和因子があるとき、行列式中心を積に分ける。
方針：第一行で余因子展開し、逆向きには第一列の残りの成分を零に取る。
規約：階数一側の像はイデアルとして与える。
使われ方：標準 étale 代数の対角成分に対応する中心の因子を取り出す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped Pointwise

/--
概要：直和に分かれた写像の階数一側の像がイデアル I なら、
全階数の行列式中心は I と残りの写像の行列式中心との積。
方針：第一行の各係数は I に入り、対応する小行列式は残りの中心に入る。
規約：残りの標的が階数零の場合も含む。
使われ方：Stacks 0813 の中心の積分解。
-/
theorem determinantalCenter_prod_line
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (I : Ideal R) (f : M →ₗ[R] (Fin n → R)) :
    determinantalCenter ((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).toLinearMap.comp
      (I.subtype.prodMap f)) = I * determinantalCenter f := by
  let g := (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).toLinearMap.comp (I.subtype.prodMap f)
  change determinantalCenter g = I * determinantalCenter f
  have hrow (v : Fin (n + 1) → I × M) (j : Fin (n + 1)) :
      imageColumnMatrix g v 0 j = (v j).1 := by
    simp [imageColumnMatrix, g]
  have hminor (v : Fin (n + 1) → I × M) (j : Fin (n + 1)) :
      (imageColumnMatrix g v).submatrix Fin.succ j.succAbove =
        imageColumnMatrix f (fun i => (v (j.succAbove i)).2) := by
    ext i k
    simp [imageColumnMatrix, g]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change (imageColumnMatrix g v).det ∈ I * determinantalCenter f
    rw [Matrix.det_succ_row_zero]
    apply Ideal.sum_mem
    intro j _
    rw [hrow, hminor, mul_assoc]
    apply Ideal.mul_mem_left
    exact Ideal.mul_mem_mul (v j).1.property
      (determinantalCenterGenerator f (fun i => (v (j.succAbove i)).2)).property
  · have hI : Ideal.span (Set.range ((↑) : I → R)) = I := by
      simp
    conv_lhs => rw [← hI, determinantalCenter, Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨v, rfl⟩, rfl⟩
    let w : Fin (n + 1) → I × M := Fin.cons (a, 0) (fun j => (0, v j))
    have hw := (determinantalCenterGenerator g w).property
    change (imageColumnMatrix g w).det ∈ determinantalCenter g at hw
    rw [Matrix.det_succ_row_zero] at hw
    simp only [hrow, hminor] at hw
    rw [Fin.sum_univ_succ] at hw
    simpa [w] using hw

end SerrePositivity.AlgebraicGeometry
