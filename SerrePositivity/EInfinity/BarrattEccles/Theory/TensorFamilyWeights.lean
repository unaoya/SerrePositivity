module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerWordWeights
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
# 有限テンソル族の次数付き基底と重み

## 概要
Berger–Moerdijk §1 の有限入力族で、異なる複体の基底と入力の重みを反復テンソルする。

## 方針
空の族を単位基底とし、先頭と残りの族に関する再帰で定義する。

## 規約
重みは非負整数で、空の族の重みは零。

## 使われ方
自由代数の演算の合成で、係数と元の入力をまとめ直す比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
variable {A : Type u} [CommRing A]

/-- The homogeneous basis indices of a finite, possibly varying tensor family. -/
def familyGradedIndex : ∀ (n : ℕ), (Fin n → ℤ → Type u) → ℤ → Type u
  | 0, _, i => unitDegreeIndex i
  | n + 1, I, i =>
      tensorGradedIndex (I 0) (familyGradedIndex n (fun j => I j.succ)) i

/-- The recursively chosen basis on the actual finite tensor family. -/
def familyGradedBasis : ∀ (n : ℕ) {V : Fin n → Complex A} {I : Fin n → ℤ → Type u},
    (∀ j i, Module.Basis (I j i) A ((V j).X i)) →
    ∀ i, Module.Basis (familyGradedIndex n I i) A ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V).X i)
  | 0, _, _, _, i => unitDegreeBasis i
  | n + 1, _, _, b, i =>
      tensorGradedBasis (b 0) (familyGradedBasis n (fun j => b j.succ)) i

/-- Total input weight, on all homogeneous indices of a finite tensor family. -/
def familyGradedWeight : ∀ (n : ℕ) {I : Fin n → ℤ → Type u},
    (∀ j, (Σ i, I j i) → ℕ) → (Σ i, familyGradedIndex n I i) → ℕ
  | 0, _, _, _ => 0
  | n + 1, _, w, x =>
      tensorGradedWeightFamily (w 0) (familyGradedWeight n (fun j => w j.succ)) x

/-- Applying a bound-preserving map in each factor preserves the total input bound. -/
lemma tensorFamilyMap_mem_basisWeightSpan (n : ℕ)
    {V W : Fin n → Complex A} {I J : Fin n → ℤ → Type u}
    (b : ∀ j i, Module.Basis (I j i) A ((V j).X i))
    (c : ∀ j i, Module.Basis (J j i) A ((W j).X i))
    (w : ∀ j, (Σ i, I j i) → ℕ) (v : ∀ j, (Σ i, J j i) → ℕ)
    (f : ∀ j, V j ⟶ W j)
    (hf : ∀ j i z, (f j).f i (b j i z) ∈
      basisWeightSpan (c j i) (fun z => v j ⟨i, z⟩) (w j ⟨i, z⟩)) :
    ∀ (i : ℤ) (N : ℕ) {x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V).X i},
      x ∈ basisWeightSpan (familyGradedBasis n b i)
        (fun z => familyGradedWeight n w ⟨i, z⟩) N →
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n f).f i x ∈ basisWeightSpan (familyGradedBasis n c i)
        (fun z => familyGradedWeight n v ⟨i, z⟩) N := by
  induction n with
  | zero => intro i N x hx; exact hx
  | succ n ih =>
    intro i N x hx
    exact tensorHom_mem_basisWeightSpan (b 0) (familyGradedBasis n (fun j => b j.succ))
      (c 0) (familyGradedBasis n (fun j => c j.succ))
      (w 0) (familyGradedWeight n (fun j => w j.succ))
      (v 0) (familyGradedWeight n (fun j => v j.succ))
      (f 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun j => f j.succ)) (hf 0)
      (fun i z => ih (fun j => b j.succ) (fun j => c j.succ)
        (fun j => w j.succ) (fun j => v j.succ) (fun j => f j.succ)
        (fun j => hf j.succ) i _
        (basis_mem_basisWeightSpan (familyGradedBasis n (fun j => b j.succ) i)
          (fun z => familyGradedWeight n (fun j => w j.succ) ⟨i, z⟩) z)) i N hx

end SerrePositivity.EInfinity
