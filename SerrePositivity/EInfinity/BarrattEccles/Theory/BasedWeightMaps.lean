module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorWordSymmetry

/-!
# 次数付き基底の重みを保つ射の合成

## 概要
Berger–Moerdijk §1 のテンソル比較で使う重み保存の証明を組み合わせる。

## 方針
基底と重みを束ね、既存のテンソル・結合子・組紐の補題を合成する。

## 規約
複体も射も既存の模型のものを使う。微分の重み保存は仮定しない。

## 使われ方
有限入力族で係数と入力を分離する比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory DifferentialGraded
variable {A : Type u} [CommRing A]

/-- A homogeneous basis with a specified nonnegative weight on each basis vector. -/
structure ComplexWeightBasis (K : Complex A) where
  index : ℤ → Type u
  basis : ∀ i, Module.Basis (index i) A (K.X i)
  weight : (Σ i, index i) → ℕ

namespace ComplexWeightBasis
variable {K L M N : Complex A}

/-- The tensor basis, weighted by the sum of the weights in its two factors. -/
abbrev tensor (b : ComplexWeightBasis K) (c : ComplexWeightBasis L) :
    ComplexWeightBasis (K ⊗ L) :=
  ⟨tensorGradedIndex b.index c.index, tensorGradedBasis b.basis c.basis,
    tensorGradedWeightFamily b.weight c.weight⟩

/-- A map preserves every bound for the two specified weighted bases. -/
def Preserves (b : ComplexWeightBasis K) (c : ComplexWeightBasis L) (f : K ⟶ L) : Prop :=
  ∀ (i : ℤ) (n : ℕ) {x : K.X i},
    x ∈ basisWeightSpan (b.basis i) (fun z => b.weight ⟨i, z⟩) n →
    f.f i x ∈ basisWeightSpan (c.basis i) (fun z => c.weight ⟨i, z⟩) n

lemma preserves_id (b : ComplexWeightBasis K) : b.Preserves b (𝟙 K) := by
  intro i n x hx
  exact hx

lemma Preserves.comp {b : ComplexWeightBasis K} {c : ComplexWeightBasis L}
    {d : ComplexWeightBasis M} {f : K ⟶ L} {g : L ⟶ M}
    (hf : b.Preserves c f) (hg : c.Preserves d g) : b.Preserves d (f ≫ g) := by
  intro i n x hx
  exact hg i n (hf i n hx)

lemma Preserves.tensor {b : ComplexWeightBasis K} {c : ComplexWeightBasis L}
    {d : ComplexWeightBasis M} {e : ComplexWeightBasis N}
    {f : K ⟶ M} {g : L ⟶ N} (hf : b.Preserves d f) (hg : c.Preserves e g) :
    (b.tensor c).Preserves (d.tensor e) (f ⊗ₘ g) := by
  intro i n x hx
  exact tensorHom_mem_basisWeightSpan b.basis c.basis d.basis e.basis
    b.weight c.weight d.weight e.weight f g
    (fun i z => hf i _ (basis_mem_basisWeightSpan (b.basis i)
      (fun z => b.weight ⟨i, z⟩) z))
    (fun i z => hg i _ (basis_mem_basisWeightSpan (c.basis i)
      (fun z => c.weight ⟨i, z⟩) z)) i n hx

lemma preserves_braiding (b : ComplexWeightBasis K) (c : ComplexWeightBasis L) :
    (b.tensor c).Preserves (c.tensor b) (β_ K L).hom :=
  tensorBraiding_mem_basisWeightSpan b.basis c.basis b.weight c.weight

lemma preserves_associator (b : ComplexWeightBasis K) (c : ComplexWeightBasis L)
    (d : ComplexWeightBasis M) :
    ((b.tensor c).tensor d).Preserves (b.tensor (c.tensor d)) (α_ K L M).hom :=
  tensorAssociator_hom_mem_basisWeightSpan b.basis c.basis d.basis b.weight c.weight d.weight

lemma preserves_associator_inv (b : ComplexWeightBasis K) (c : ComplexWeightBasis L)
    (d : ComplexWeightBasis M) :
    (b.tensor (c.tensor d)).Preserves ((b.tensor c).tensor d) (α_ K L M).inv :=
  tensorAssociator_inv_mem_basisWeightSpan b.basis c.basis d.basis b.weight c.weight d.weight

/-- The middle interchange, including its Koszul sign, preserves total input weights. -/
lemma preserves_tensorμ (b : ComplexWeightBasis K) (c : ComplexWeightBasis L)
    (d : ComplexWeightBasis M) (e : ComplexWeightBasis N) :
    ((b.tensor c).tensor (d.tensor e)).Preserves ((b.tensor d).tensor (c.tensor e))
      (tensorμ K L M N) := by
  have h₁ := preserves_associator b c (d.tensor e)
  have h₂ := (preserves_id b).tensor (preserves_associator_inv c d e)
  have h₃ := (preserves_id b).tensor ((preserves_braiding c d).tensor (preserves_id e))
  have h₄ := (preserves_id b).tensor (preserves_associator d c e)
  have h₅ := preserves_associator_inv b d (c.tensor e)
  simpa only [tensorμ, id_tensorHom, tensorHom_id] using
    h₁.comp (h₂.comp (h₃.comp (h₄.comp h₅)))

end ComplexWeightBasis
end SerrePositivity.EInfinity
