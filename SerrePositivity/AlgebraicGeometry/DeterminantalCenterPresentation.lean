module

public import SerrePositivity.AlgebraicGeometry.DeterminantalCenter
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdealColumnSpan

/-!
概要：行列式中心を有限な表示行列の最大小行列式イデアルと比較する。
方針：列の生成する部分加群を比較し、全行を選ぶ小行列式だけを残す。
規約：標的は有限階数自由加群の座標で固定する。
使われ方：Stacks 0813 の中心で、行列式イデアルを底変換や基底変更へ移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

/--
概要：像を生成する有限な列を持つ行列を選ぶと、行列式中心は最大小行列式イデアルに等しい。
方針：任意の像の列は生成列の線形結合であり、最大小行列式の行選択は置換か重複行を与える。
規約：階数零を含み、生成列の独立性は要求しない。
使われ方：行列式中心を行列の底変換公式で扱う。
-/
theorem determinantalCenter_eq_matrixMinorIdeal
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι] {n : ℕ}
    (g : M →ₗ[R] (Fin n → R)) (B : Matrix (Fin n) ι R)
    (hB : Submodule.span R (Set.range B.col) = LinearMap.range g) :
    determinantalCenter g = matrixMinorIdeal B n := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v, rfl⟩
    refine matrixMinorIdeal_le_of_columnSpan_le (imageColumnMatrix g v) B ?_ n ?_
    · rw [hB, Submodule.span_le]
      intro x hx
      obtain ⟨j, rfl⟩ := hx
      exact ⟨v j, rfl⟩
    · exact det_submatrix_mem_matrixMinorIdeal _ n id id
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨r, c⟩, rfl⟩
    change (B.submatrix r c).det ∈ determinantalCenter g
    by_cases hr : Function.Injective r
    · let σ := Equiv.ofBijective r (Finite.injective_iff_bijective.mp hr)
      have hcol (j : Fin n) : B.col (c j) ∈ LinearMap.range g :=
        hB ▸ Submodule.subset_span ⟨c j, rfl⟩
      choose v hv using hcol
      have hmat : B.submatrix r c = (imageColumnMatrix g v).submatrix σ id := by
        ext i j
        exact (congrFun (hv j) (r i)).symm
      rw [hmat, Matrix.det_permute]
      exact Ideal.mul_mem_left _ _ (determinantalCenterGenerator g v).property
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hr
      have hrow : B.submatrix r c i = B.submatrix r c j :=
        funext fun k => congrArg (fun t => B t (c k)) hij
      rw [Matrix.det_zero_of_row_eq hne hrow]
      exact Ideal.zero_mem _

end SerrePositivity.AlgebraicGeometry
