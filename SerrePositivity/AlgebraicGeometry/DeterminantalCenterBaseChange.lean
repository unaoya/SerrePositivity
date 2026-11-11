module

public import SerrePositivity.AlgebraicGeometry.DeterminantalCenterPresentation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
概要：有限自由加群の行列式中心を座標変更と底変換に移す。
方針：座標変更では正方行列の積を使い、底変換では有限な生成列の最大小行列式を比較する。
規約：自由加群の基底は有限の添字集合 Fin n で表す。
使われ方：Stacks 0813 で、基底側の中心を標準 étale の対角分解と照合する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem determinantalCenter_postcomp_le
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] (Fin n → R)) :
    determinantalCenter (g.comp f) ≤ determinantalCenter f := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v, rfl⟩
  change (imageColumnMatrix (g.comp f) v).det ∈ determinantalCenter f
  have h : imageColumnMatrix (g.comp f) v = g.toMatrix' * imageColumnMatrix f v := by
    ext i j
    exact (congrFun (LinearMap.toMatrix'_mulVec g (f (v j))) i).symm
  rw [h, Matrix.det_mul]
  exact Ideal.mul_mem_left _ _ (determinantalCenterGenerator f v).property

/--
概要：標的の自由加群で座標を変えても、行列式中心は同じイデアルになる。
方針：座標変換の行列を掛けると行列式がその行列式倍となり、逆の座標変換も使える。
規約：標的の座標は Fin n で添字付ける。
使われ方：標準 étale の底変換先で直積に適合する基底へ移る。
-/
theorem determinantalCenter_postcomp_linearEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M →ₗ[R] (Fin n → R)) (e : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    determinantalCenter (e.toLinearMap.comp f) = determinantalCenter f := by
  apply le_antisymm (determinantalCenter_postcomp_le f e.toLinearMap)
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id :=
    LinearMap.ext e.symm_apply_apply
  have h := determinantalCenter_postcomp_le (e.toLinearMap.comp f) e.symm.toLinearMap
  rwa [← LinearMap.comp_assoc, he, LinearMap.id_comp] at h

/--
概要：有限自由加群の有限生成部分加群の行列式中心は、底変換した部分加群の中心へ写る。
方針：生成列を行列にし、底変換した列が底変換した部分加群を生成することを使う。
規約：底変換写像の平坦性を仮定せず、底変換した部分加群はテンソル写像の像を取る。
使われ方：基底側で作った中心を、標準 étale の分解先に送る。
-/
theorem determinantalCenter_submodule_baseChange
    {R B C : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup C] [Module R C] {n : ℕ}
    (b : Module.Basis (Fin n) R C) (P : Submodule R C) (hP : P.FG) :
    (determinantalCenter (b.equivFun.toLinearMap.comp P.subtype)).map (algebraMap R B) =
      determinantalCenter
        ((b.baseChange B).equivFun.toLinearMap.comp (P.baseChange B).subtype) := by
  classical
  obtain ⟨s, hs⟩ := hP
  let X : Matrix (Fin n) s R := fun i j => b.equivFun j i
  have hcols : Set.range X.col = b.equivFun '' (s : Set C) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hcolsB : Set.range (X.map (algebraMap R B)).col =
      (b.baseChange B).equivFun '' (TensorProduct.mk R B C 1 '' (s : Set C)) := by
    have h (j : s) : (X.map (algebraMap R B)).col j = (b.baseChange B).equivFun (1 ⊗ₜ[R] ↑j) := by
      funext i
      change algebraMap R B (b.equivFun j i) = (b.baseChange B).equivFun (1 ⊗ₜ[R] ↑j) i
      simp [Module.Basis.equivFun_apply, Algebra.smul_def]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨1 ⊗ₜ[R] ↑j, ⟨j, j.property, rfl⟩, (h j).symm⟩
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨j, hj⟩, h ⟨j, hj⟩⟩
  have hspan : Submodule.span R (Set.range X.col) =
      LinearMap.range (b.equivFun.toLinearMap.comp P.subtype) := by
    rw [hcols]
    change Submodule.span R (b.equivFun.toLinearMap '' (s : Set C)) = _
    rw [← Submodule.map_span, hs, LinearMap.range_comp, Submodule.range_subtype]
  have hspanB : Submodule.span B (Set.range (X.map (algebraMap R B)).col) =
      LinearMap.range ((b.baseChange B).equivFun.toLinearMap.comp (P.baseChange B).subtype) := by
    rw [hcolsB]
    change Submodule.span B ((b.baseChange B).equivFun.toLinearMap ''
      (TensorProduct.mk R B C 1 '' (s : Set C))) = _
    rw [← Submodule.map_span, LinearMap.range_comp, Submodule.range_subtype,
      ← hs, Submodule.baseChange_span]
  rw [determinantalCenter_eq_matrixMinorIdeal _ X hspan, matrixMinorIdeal_map,
    ← determinantalCenter_eq_matrixMinorIdeal _ _ hspanB]

end SerrePositivity.AlgebraicGeometry
