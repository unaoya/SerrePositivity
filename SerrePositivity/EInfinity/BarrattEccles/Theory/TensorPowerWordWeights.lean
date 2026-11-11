module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorWordSymmetry
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation

/-!
# テンソル冪の入力置換と語の重み

## 概要
Berger–Moerdijk §1 の対称群作用が、入力の語の総重みの上限を保つ。

## 方針
括り直しと Koszul の交換から隣接互換を扱い、隣接互換による生成を使う。

## 規約
零入力と各入力の重複を含める。

## 使われ方
Schur の余不変の正規化で重みが増えないことの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open SerrePositivity.Coxeter
variable {A : Type u} [CommRing A] {K : Complex A} {I : ℤ → Type u}
  (b : ∀ i, Module.Basis (I i) A (K.X i)) (w : (Σ i, I i) → ℕ)

/-- The power-word weight on all homogeneous basis indices. -/
def powerGradedWeightFamily (n : ℕ) : (Σ i, powerGradedIndex I n i) → ℕ :=
  fun x => powerGradedWeight w n x.1 x.2

lemma powerGradedBasis_succ (n : ℕ) :
    powerGradedBasis b (n + 1) = tensorGradedBasis b (powerGradedBasis b n) := rfl

lemma powerGradedWeight_succ (n : ℕ) :
    powerGradedWeight w (n + 1) =
      tensorGradedWeight w (powerGradedWeightFamily w n) := by
  funext i ⟨a, x, y⟩
  rfl

lemma powerGradedWeightFamily_succ (n : ℕ) :
    powerGradedWeightFamily w (n + 1) =
      tensorGradedWeightFamily w (powerGradedWeightFamily w n) := by
  funext ⟨i, a, x, y⟩
  rfl

/-- Adding an unchanged first input preserves bounds when the tail map does. -/
lemma powerWhisker_mem_basisWeightSpan (n : ℕ)
    (f : power K n ⟶ power K n)
    (hf : ∀ i N {x : (power K n).X i},
      x ∈ basisWeightSpan (powerGradedBasis b n i) (powerGradedWeight w n i) N →
      f.f i x ∈ basisWeightSpan (powerGradedBasis b n i) (powerGradedWeight w n i) N)
    (i : ℤ) (N : ℕ) {x : (power K (n + 1)).X i}
    (hx : x ∈ basisWeightSpan (powerGradedBasis b (n + 1) i)
      (powerGradedWeight w (n + 1) i) N) :
    (K ◁ f).f i x ∈ basisWeightSpan (powerGradedBasis b (n + 1) i)
      (powerGradedWeight w (n + 1) i) N := by
  have h₀ : x ∈ basisWeightSpan (tensorGradedBasis b (powerGradedBasis b n) i)
      (tensorGradedWeight w (powerGradedWeightFamily w n) i) N := by
    simpa only [powerGradedBasis_succ, powerGradedWeightFamily,
      powerGradedWeight_succ, tensorGradedWeightFamily] using hx
  have h := tensorHom_mem_basisWeightSpan b (powerGradedBasis b n) b (powerGradedBasis b n)
    w (powerGradedWeightFamily w n)
    w (powerGradedWeightFamily w n) (𝟙 K) f
    (fun i z => by simpa using basis_mem_basisWeightSpan (b i) (fun z => w ⟨i, z⟩) z)
    (fun i z => hf i _ (basis_mem_basisWeightSpan (powerGradedBasis b n i)
      (powerGradedWeight w n i) z)) i N h₀
  simpa only [id_tensorHom, powerGradedBasis_succ, powerGradedWeightFamily,
    powerGradedWeight_succ, tensorGradedWeightFamily] using h

/-- Exchanging the first two inputs preserves their total weight together with the tail. -/
lemma swapFirst_mem_basisWeightSpan (n : ℕ) (i : ℤ) (N : ℕ)
    {x : (power K (n + 2)).X i}
    (hx : x ∈ basisWeightSpan (powerGradedBasis b (n + 2) i)
      (powerGradedWeight w (n + 2) i) N) :
    (swapFirstIso K n).hom.f i x ∈ basisWeightSpan (powerGradedBasis b (n + 2) i)
      (powerGradedWeight w (n + 2) i) N := by
  let t : (Σ i, powerGradedIndex I n i) → ℕ :=
    powerGradedWeightFamily w n
  have h₀ : x ∈ basisWeightSpan (tensorGradedBasis b (tensorGradedBasis b (powerGradedBasis b n)) i)
      (tensorGradedWeight w (tensorGradedWeightFamily w t) i) N := by
    simp only [powerGradedBasis_succ, powerGradedWeight_succ,
      powerGradedWeightFamily_succ, t] at hx ⊢
    exact hx
  have h₁ := tensorAssociator_inv_mem_basisWeightSpan b b (powerGradedBasis b n)
    w w t i N h₀
  have h₂ := tensorHom_mem_basisWeightSpan (tensorGradedBasis b b) (powerGradedBasis b n)
    (tensorGradedBasis b b) (powerGradedBasis b n)
    (tensorGradedWeightFamily w w) t
    (tensorGradedWeightFamily w w) t (β_ K K).hom (𝟙 _)
    (fun i z => tensorBraiding_mem_basisWeightSpan b b w w i _
      (basis_mem_basisWeightSpan (tensorGradedBasis b b i) (tensorGradedWeight w w i) z))
    (fun i z => by
      exact basis_mem_basisWeightSpan (powerGradedBasis b n i)
        (fun z => t ⟨i, z⟩) z) i N h₁
  have h₃ := tensorAssociator_hom_mem_basisWeightSpan b b (powerGradedBasis b n)
    w w t i N h₂
  simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    tensorHom_id, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    powerGradedBasis_succ, powerGradedWeight_succ, powerGradedWeightFamily_succ,
    t] at h₃ ⊢
  exact h₃

/-- Every adjacent input exchange preserves the specified power-word filtration. -/
lemma adjacent_mem_basisWeightSpan (n : ℕ) (j : Fin n) :
    ∀ (i : ℤ) (N : ℕ) {x : (power K (n + 1)).X i},
      x ∈ basisWeightSpan (powerGradedBasis b (n + 1) i)
        (powerGradedWeight w (n + 1) i) N →
      (adjacentIso K n j).hom.f i x ∈ basisWeightSpan (powerGradedBasis b (n + 1) i)
        (powerGradedWeight w (n + 1) i) N := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · intro i N x hx
      exact swapFirst_mem_basisWeightSpan b w n i N hx
    · intro i N x hx
      exact powerWhisker_mem_basisWeightSpan b w (n + 1) (adjacentIso K n j).hom
        (ih j) i N hx

/-- Every symmetric-group input action preserves the total input weight bound. -/
lemma permutationAction_mem_basisWeightSpan (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∀ (i : ℤ) (N : ℕ) {x : (power K n).X i},
      x ∈ basisWeightSpan (powerGradedBasis b n i) (powerGradedWeight w n i) N →
      (permutationAction K n σ).asIso.hom.f i x ∈
        basisWeightSpan (powerGradedBasis b n i) (powerGradedWeight w n i) N := by
  cases n with
  | zero =>
    intro i N x hx
    rw [permutationAction_zero]
    exact hx
  | succ n =>
    have hσ : σ ∈ Submonoid.closure (Set.range (@adjacentTransposition n)) := by
      rw [show (@adjacentTransposition n) =
        (fun i : Fin n => Equiv.swap i.castSucc i.succ) from rfl,
        Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem σ hσ =>
      obtain ⟨j, rfl⟩ := hσ
      intro i N x hx
      rw [permutationAction_adjacent]
      exact adjacent_mem_basisWeightSpan b w n j i N hx
    | one =>
      intro i N x hx
      rw [permutationAction_one]
      exact hx
    | mul σ τ _ _ hσ hτ =>
      intro i N x hx
      rw [permutationAction_mul, HomologicalComplex.comp_f, ModuleCat.comp_apply]
      exact hσ i N (hτ i N hx)

end SerrePositivity.EInfinity
