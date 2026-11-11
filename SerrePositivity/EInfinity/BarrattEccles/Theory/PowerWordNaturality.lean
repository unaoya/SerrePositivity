module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.PowerWordEvaluation

/-!
# 指定入力のテンソル語の自然性

## 概要
Berger–Moerdijk §1 の反復テンソルで、語の評価を複体の射で移す。

## 方針
テンソル冪の長さで帰納し、斉次テンソルの写像の式を使う。

## 規約
指定入力は基底である必要はなく、零入力も含める。

## 使われ方
微分を消した自由代数と実際のセル段の作用の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {K L : Complex A} {I : ℤ → Type u}

/-- A map of complexes carries an evaluated input word to the word of its input images. -/
lemma powerWordValue_naturality (f : K ⟶ L) (g : ∀ i, I i → K.X i)
    (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) :
    (TensorPowers.map f n).f i (powerWordValue K g n i x) =
      powerWordValue L (fun i z => f.f i (g i z)) n i x := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    obtain ⟨a, z, y⟩ := x
    change (cochainTensorMap f (TensorPowers.map f n)).f i
      (ιTensorObj K (power K n) a.1.1 a.1.2 i a.2
        (g a.1.1 z ⊗ₜ[A] powerWordValue K g n a.1.2 y)) = _
    rw [cochainTensorMap_apply_ι, ih]
    rfl

/-- A map identifying the input bases identifies the specified bases on every tensor power. -/
lemma powerGradedBasis_map (f : K ⟶ L)
    (b : ∀ i, Module.Basis (I i) A (K.X i))
    (c : ∀ i, Module.Basis (I i) A (L.X i))
    (hf : ∀ i z, f.f i (b i z) = c i z)
    (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) :
    (TensorPowers.map f n).f i (powerGradedBasis b n i x) = powerGradedBasis c n i x := by
  have h := powerWordValue_naturality f (fun i z => b i z) n i x
  have he : (fun i z => f.f i (b i z)) = (fun i z => c i z) := by
    funext i z
    exact hf i z
  rw [he, powerWordValue_basis, powerWordValue_basis] at h
  exact h

end SerrePositivity.EInfinity
