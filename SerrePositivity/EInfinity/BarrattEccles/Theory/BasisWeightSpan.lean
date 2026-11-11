module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# 基底の重みで定める線形包

## 概要
Berger–Moerdijk 命題 4.1 のセル代数で、入力の重みが定める線形包を扱う。

## 方針
基底の座標の有限台による判定と、線形写像・テンソル積での保存を使う。

## 規約
重みの上限を含む線形包を取る。

## 使われ方
Schur の語の重みと、代数の作用・微分の照合。
-/

@[expose] public noncomputable section

universe u v w v' w'

namespace SerrePositivity.EInfinity

open scoped TensorProduct

variable {R : Type u} [CommRing R]
  {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type w} [AddCommGroup W] [Module R W]
  {I : Type v'} {J : Type w'}

/-- The span of the basis vectors whose weights are at most the bound. -/
def basisWeightSpan (b : Module.Basis I R V) (w : I → ℕ) (n : ℕ) : Submodule R V :=
  Submodule.span R (b '' {i | w i ≤ n})

lemma basisWeightSpan_mono (b : Module.Basis I R V) (w : I → ℕ)
    {n m : ℕ} (h : n ≤ m) : basisWeightSpan b w n ≤ basisWeightSpan b w m :=
  Submodule.span_mono (Set.image_mono (fun _ hi => hi.trans h))

/-- Weight membership can be checked on the support of the specified coordinates. -/
lemma mem_basisWeightSpan (b : Module.Basis I R V) (w : I → ℕ) (n : ℕ) (x : V) :
    x ∈ basisWeightSpan b w n ↔ ∀ i ∈ (b.repr x).support, w i ≤ n :=
  b.mem_span_image

lemma basis_mem_basisWeightSpan (b : Module.Basis I R V) (w : I → ℕ) (i : I) :
    b i ∈ basisWeightSpan b w (w i) :=
  Submodule.subset_span ⟨i, (show w i ≤ w i from le_refl _), rfl⟩

/-- Checking the images of the basis vectors suffices to control every bounded span. -/
lemma map_mem_basisWeightSpan (b : Module.Basis I R V) (c : Module.Basis J R W)
    (w : I → ℕ) (v : J → ℕ) (f : V →ₗ[R] W)
    (hf : ∀ i, f (b i) ∈ basisWeightSpan c v (w i))
    (n : ℕ) {x : V} (hx : x ∈ basisWeightSpan b w n) :
    f x ∈ basisWeightSpan c v n := by
  have h : basisWeightSpan b w n ≤ (basisWeightSpan c v n).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact basisWeightSpan_mono c v hi (hf i)
  exact h hx

/-- Tensoring vectors adds their weight bounds, with respect to the specified tensor basis. -/
lemma tensor_mem_basisWeightSpan (b : Module.Basis I R V) (c : Module.Basis J R W)
    (w : I → ℕ) (v : J → ℕ) (n m : ℕ) {x : V} {y : W}
    (hx : x ∈ basisWeightSpan b w n) (hy : y ∈ basisWeightSpan c v m) :
    x ⊗ₜ[R] y ∈ basisWeightSpan (b.tensorProduct c) (fun a => w a.1 + v a.2) (n + m) := by
  let S := basisWeightSpan (b.tensorProduct c) (fun a => w a.1 + v a.2) (n + m)
  have hright (i : I) (hi : w i ≤ n) :
      basisWeightSpan c v m ≤ S.comap ((TensorProduct.mk R V W) (b i)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change b i ⊗ₜ[R] c j ∈ S
    apply Submodule.subset_span
    refine ⟨(i, j), Nat.add_le_add hi hj, ?_⟩
    exact Module.Basis.tensorProduct_apply b c i j
  have hleft : basisWeightSpan b w n ≤ S.comap ((TensorProduct.mk R V W).flip y) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hright i hi hy
  exact hleft hx

end SerrePositivity.EInfinity
