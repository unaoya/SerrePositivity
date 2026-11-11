module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerDegreeBasis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BasisWeightSpan

/-!
# 斉次テンソルの語の重み

## 概要
Berger–Moerdijk §1 の演算の入力で、テンソルを取った語の総重みを比較する。

## 方針
指定基底の包含式を使い、重み付き部分加群のテンソルの評価を全次数へ移す。

## 規約
総重みは各入力の重みの和。

## 使われ方
セルの語の微分と演算の合成による重みの保存。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- The two homogeneous degrees and the two corresponding basis indices. -/
abbrev tensorGradedIndex (I J : ℤ → Type u) (i : ℤ) :=
  Σ a : {a : ℤ × ℤ // a.1 + a.2 = i}, I a.1.1 × J a.1.2

/-- The weight of a tensor basis vector is the sum of the weights of its two inputs. -/
def tensorGradedWeight {I J : ℤ → Type u}
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ) (i : ℤ)
    (x : tensorGradedIndex I J i) : ℕ :=
  w ⟨x.1.1.1, x.2.1⟩ + v ⟨x.1.1.2, x.2.2⟩

/-- The same total weight as a function on all homogeneous tensor basis indices. -/
def tensorGradedWeightFamily {I J : ℤ → Type u}
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ) :
    (Σ i, tensorGradedIndex I J i) → ℕ :=
  fun x => tensorGradedWeight w v x.1 x.2

/-- The homogeneous tensor inclusion adds the two input weight bounds. -/
lemma tensorGradedInclusion_mem {K L : Complex A} {I J : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i))
    (c : ∀ i, Module.Basis (J i) A (L.X i))
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ)
    (p r i : ℤ) (h : p + r = i) (m n : ℕ)
    {x : K.X p} {y : L.X r}
    (hx : x ∈ basisWeightSpan (b p) (fun z => w ⟨p, z⟩) m)
    (hy : y ∈ basisWeightSpan (c r) (fun z => v ⟨r, z⟩) n) :
    ιTensorObj K L p r i h (x ⊗ₜ[A] y) ∈
      basisWeightSpan (tensorGradedBasis b c i) (tensorGradedWeight w v i) (m + n) := by
  have ht := tensor_mem_basisWeightSpan (b p) (c r)
    (fun z => w ⟨p, z⟩) (fun z => v ⟨r, z⟩) m n hx hy
  apply map_mem_basisWeightSpan ((b p).tensorProduct (c r))
    (tensorGradedBasis b c i) (fun z => w ⟨p, z.1⟩ + v ⟨r, z.2⟩)
    (tensorGradedWeight w v i) (ιTensorObj K L p r i h).hom ?_ (m + n) ht
  intro z
  erw [Module.Basis.tensorProduct_apply' (b p) (c r) z]
  have hz := basis_mem_basisWeightSpan (tensorGradedBasis b c i)
    (tensorGradedWeight w v i) ⟨⟨(p, r), h⟩, z⟩
  rw [tensorGradedBasis_apply] at hz
  exact hz

/-- Tensor products of maps that preserve basis weight bounds preserve the total bounds. -/
lemma tensorHom_mem_basisWeightSpan
    {K L K' L' : Complex A} {I J I' J' : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i))
    (c : ∀ i, Module.Basis (J i) A (L.X i))
    (b' : ∀ i, Module.Basis (I' i) A (K'.X i))
    (c' : ∀ i, Module.Basis (J' i) A (L'.X i))
    (w : (Σ i, I i) → ℕ) (v : (Σ i, J i) → ℕ)
    (w' : (Σ i, I' i) → ℕ) (v' : (Σ i, J' i) → ℕ)
    (f : K ⟶ K') (g : L ⟶ L')
    (hf : ∀ i z, f.f i (b i z) ∈ basisWeightSpan (b' i) (fun z => w' ⟨i, z⟩) (w ⟨i, z⟩))
    (hg : ∀ i z, g.f i (c i z) ∈ basisWeightSpan (c' i) (fun z => v' ⟨i, z⟩) (v ⟨i, z⟩))
    (i : ℤ) (N : ℕ) {x : (K ⊗ L).X i}
    (hx : x ∈ basisWeightSpan (tensorGradedBasis b c i) (tensorGradedWeight w v i) N) :
    (f ⊗ₘ g).f i x ∈
      basisWeightSpan (tensorGradedBasis b' c' i) (tensorGradedWeight w' v' i) N := by
  apply map_mem_basisWeightSpan (tensorGradedBasis b c i) (tensorGradedBasis b' c' i)
    (tensorGradedWeight w v i) (tensorGradedWeight w' v' i) ((f ⊗ₘ g).f i).hom ?_ N hx
  rintro ⟨a, z, t⟩
  rw [tensorGradedBasis_apply]
  have he : (f ⊗ₘ g).f i
      (ιTensorObj K L a.1.1 a.1.2 i a.2 (b a.1.1 z ⊗ₜ[A] c a.1.2 t)) =
      ιTensorObj K' L' a.1.1 a.1.2 i a.2
        (f.f a.1.1 (b a.1.1 z) ⊗ₜ[A] g.f a.1.2 (c a.1.2 t)) := by
    change (ιTensorObj K L a.1.1 a.1.2 i a.2 ≫ (cochainTensorMap f g).f i) _ = _
    rw [ιTensorObj_cochainTensorMap]
    rfl
  rw [he]
  exact tensorGradedInclusion_mem b' c' w' v' a.1.1 a.1.2 i a.2
    (w ⟨a.1.1, z⟩) (v ⟨a.1.2, t⟩) (hf _ _) (hg _ _)

end SerrePositivity.EInfinity
