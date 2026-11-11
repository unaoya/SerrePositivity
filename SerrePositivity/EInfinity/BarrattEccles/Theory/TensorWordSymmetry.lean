module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorWordWeights
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-!
# Koszul の交換と括り直しによる重みの保存

## 概要
Berger–Moerdijk §1 の入力の置換と合成で、語の総重みの上限を保つ。

## 方針
指定基底ベクトル上の斉次テンソルの公式を使う。Koszul の符号は部分加群を保つ。

## 規約
括り直しの前後で各入力の出現回数を保持する。

## 使われ方
セル代数の演算と微分の重みの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- The Koszul braiding preserves the total weight bound of a homogeneous tensor. -/
lemma tensorBraiding_mem_basisWeightSpan {K L : Complex A} {I J : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i))
    (c : ∀ i, Module.Basis (J i) A (L.X i))
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ)
    (i : ℤ) (N : ℕ) {x : (K ⊗ L).X i}
    (hx : x ∈ basisWeightSpan (tensorGradedBasis b c i) (tensorGradedWeight w v i) N) :
    (β_ K L).hom.f i x ∈
      basisWeightSpan (tensorGradedBasis c b i) (tensorGradedWeight v w i) N := by
  apply map_mem_basisWeightSpan (tensorGradedBasis b c i) (tensorGradedBasis c b i)
    (tensorGradedWeight w v i) (tensorGradedWeight v w i) ((β_ K L).hom.f i).hom ?_ N hx
  rintro ⟨a, z, t⟩
  rw [tensorGradedBasis_apply]
  change (cochainTensorSymmetry K L).hom.f i
    (ιTensorObj K L a.1.1 a.1.2 i a.2 (b a.1.1 z ⊗ₜ[A] c a.1.2 t)) ∈ _
  rw [cochainTensorSymmetry_hom_apply_ι]
  have hz := basis_mem_basisWeightSpan (tensorGradedBasis c b i)
    (tensorGradedWeight v w i) ⟨⟨(a.1.2, a.1.1), by omega⟩, t, z⟩
  rw [tensorGradedBasis_apply] at hz
  have hy : ιTensorObj L K a.1.2 a.1.1 i (by omega)
      (c a.1.2 t ⊗ₜ[A] b a.1.1 z) ∈
      basisWeightSpan (tensorGradedBasis c b i) (tensorGradedWeight v w i)
        (tensorGradedWeight w v i ⟨a, z, t⟩) := by
    simpa only [tensorGradedWeight, Nat.add_comm] using hz
  simpa only [Units.smul_def] using zsmul_mem hy (a.1.1 * a.1.2).negOnePow.val

/-- The forward associator preserves the sum of the three input weights. -/
lemma tensorAssociator_hom_mem_basisWeightSpan
    {K L M : Complex A} {I J H : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i))
    (c : ∀ i, Module.Basis (J i) A (L.X i))
    (d : ∀ i, Module.Basis (H i) A (M.X i))
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ) (t : (Σ i, H i) → ℕ)
    (i : ℤ) (N : ℕ) {x : ((K ⊗ L) ⊗ M).X i}
    (hx : x ∈ basisWeightSpan (tensorGradedBasis (tensorGradedBasis b c) d i)
      (tensorGradedWeight (tensorGradedWeightFamily w v) t i) N) :
    (α_ K L M).hom.f i x ∈
      basisWeightSpan (tensorGradedBasis b (tensorGradedBasis c d) i)
        (tensorGradedWeight w (tensorGradedWeightFamily v t) i) N := by
  apply map_mem_basisWeightSpan (tensorGradedBasis (tensorGradedBasis b c) d i)
    (tensorGradedBasis b (tensorGradedBasis c d) i)
    (tensorGradedWeight (tensorGradedWeightFamily w v) t i)
    (tensorGradedWeight w (tensorGradedWeightFamily v t) i)
    ((α_ K L M).hom.f i).hom ?_ N hx
  rintro ⟨a, ⟨s, z, y⟩, r⟩
  rw [tensorGradedBasis_apply, tensorGradedBasis_apply]
  change (cochainTensorAssociator K L M).hom.f i
    (ιTensorObj (K ⊗ L) M a.1.1 a.1.2 i a.2
      (ιTensorObj K L s.1.1 s.1.2 a.1.1 s.2
        (b s.1.1 z ⊗ₜ[A] c s.1.2 y) ⊗ₜ[A] d a.1.2 r)) ∈ _
  erw [cochainTensorAssociator_hom_apply_ι_of_sum]
  have hz := basis_mem_basisWeightSpan (tensorGradedBasis b (tensorGradedBasis c d) i)
    (tensorGradedWeight w (tensorGradedWeightFamily v t) i)
      ⟨⟨(s.1.1, s.1.2 + a.1.2), by omega⟩, z, ⟨⟨(s.1.2, a.1.2), rfl⟩, y, r⟩⟩
  rw [tensorGradedBasis_apply, tensorGradedBasis_apply] at hz
  simp only [tensorGradedWeight, tensorGradedWeightFamily, Nat.add_assoc] at hz ⊢
  exact hz

/-- The inverse associator preserves the sum of the three input weights. -/
lemma tensorAssociator_inv_mem_basisWeightSpan
    {K L M : Complex A} {I J H : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i))
    (c : ∀ i, Module.Basis (J i) A (L.X i))
    (d : ∀ i, Module.Basis (H i) A (M.X i))
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ) (t : (Σ i, H i) → ℕ)
    (i : ℤ) (N : ℕ) {x : (K ⊗ (L ⊗ M)).X i}
    (hx : x ∈ basisWeightSpan (tensorGradedBasis b (tensorGradedBasis c d) i)
      (tensorGradedWeight w (tensorGradedWeightFamily v t) i) N) :
    (α_ K L M).inv.f i x ∈
      basisWeightSpan (tensorGradedBasis (tensorGradedBasis b c) d i)
        (tensorGradedWeight (tensorGradedWeightFamily w v) t i) N := by
  apply map_mem_basisWeightSpan (tensorGradedBasis b (tensorGradedBasis c d) i)
    (tensorGradedBasis (tensorGradedBasis b c) d i)
    (tensorGradedWeight w (tensorGradedWeightFamily v t) i)
    (tensorGradedWeight (tensorGradedWeightFamily w v) t i)
    ((α_ K L M).inv.f i).hom ?_ N hx
  rintro ⟨a, z, ⟨s, y, r⟩⟩
  rw [tensorGradedBasis_apply, tensorGradedBasis_apply]
  change (cochainTensorAssociator K L M).inv.f i
    (ιTensorObj K (L ⊗ M) a.1.1 a.1.2 i a.2
      (b a.1.1 z ⊗ₜ[A] ιTensorObj L M s.1.1 s.1.2 a.1.2 s.2
        (c s.1.1 y ⊗ₜ[A] d s.1.2 r))) ∈ _
  erw [cochainTensorAssociator_inv_apply_ι_of_sum]
  have hz := basis_mem_basisWeightSpan (tensorGradedBasis (tensorGradedBasis b c) d i)
    (tensorGradedWeight (tensorGradedWeightFamily w v) t i)
      ⟨⟨(a.1.1 + s.1.1, s.1.2), by omega⟩, ⟨⟨(a.1.1, s.1.1), rfl⟩, z, y⟩, r⟩
  rw [tensorGradedBasis_apply, tensorGradedBasis_apply] at hz
  simp only [tensorGradedWeight, tensorGradedWeightFamily, Nat.add_assoc] at hz ⊢
  exact hz

end SerrePositivity.EInfinity
