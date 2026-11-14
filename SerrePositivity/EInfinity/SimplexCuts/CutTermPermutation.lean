module

public import SerrePositivity.EInfinity.SimplexCuts.CutVectorsRenaming
public import SerrePositivity.EInfinity.SimplexCuts.CutRenamingSigns
public import SerrePositivity.EInfinity.SimplexCuts.TensorAdjacentSwap
public import SerrePositivity.EInfinity.SimplexCuts.SignedTerms
public import SerrePositivity.GroupTheory.Coxeter.PermutationInduction

/-!
# 同じ一般切断項の出力の置換

Berger–Fresse §2.2.4–6、M14 L11 の証明分割。
同じ指定面の因子と切断係数を、元の Koszul 置換の射へ合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C339：同じ面テンソルの隣接交換は、二つの出力次数の符号を持つ（BF §2.2.4）。 -/
lemma cutTensorAt_adjacent {m q n : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word (n + 1) (m + 1)) (a : Fin n) (x : S _⦋q⦌) :
    (adjacentIso (chains A S) n a).hom.f (-((m + q + 1 - (n + 1) : ℕ) : ℤ))
        (cutTensorAt A S s v x) =
      (-1 : ℤ) ^ (outputDegree s v a.castSucc * outputDegree s v a.succ) •
        cutTensorAt A S s (Surjection.Word.rename (adjacentTransposition a) v) x := by
  have hf : (fun b => cutVector A S s (Surjection.Word.rename (adjacentTransposition a) v) b x) =
      (fun b => cutVector A S s v b x) ∘ adjacentTransposition a := by
    simpa only [adjacentTransposition, Equiv.symm_swap] using
      cutVector_rename A S s v (adjacentTransposition a) x
  have hdeg : -(vectorDegree (chains A S) (n + 1) (fun b => cutVector A S s v b x) : ℤ) =
      -((m + q + 1 - (n + 1) : ℕ) : ℤ) := by
    change -(degreeSum (n + 1) (outputDegree s v) : ℤ) = _
    rw [degreeSum_eq_sum, outputDegree_sum]
  have H := adjacentIso_vectorTensorAt (chains A S) n a
    (fun b => cutVector A S s v b x) (-((m + q + 1 - (n + 1) : ℕ) : ℤ)) hdeg
  have hdeg' : -(vectorDegree (chains A S) (n + 1)
      (fun b => cutVector A S s (Surjection.Word.rename (adjacentTransposition a) v) b x) : ℤ) =
      -((m + q + 1 - (n + 1) : ℕ) : ℤ) := by
    change -(degreeSum (n + 1)
      (outputDegree s (Surjection.Word.rename (adjacentTransposition a) v)) : ℤ) = _
    rw [degreeSum_eq_sum, outputDegree_sum]
  have heval := vectorTensorAt_congr (chains A S) (n + 1)
    ((fun b => cutVector A S s v b x) ∘ adjacentTransposition a)
    (fun b => cutVector A S s (Surjection.Word.rename (adjacentTransposition a) v) b x)
    (-((m + q + 1 - (n + 1) : ℕ) : ℤ))
    (by rw [vectorDegree_permutation]; exact hdeg) hdeg' hf.symm
  rw [heval] at H
  unfold cutTensorAt
  rw [← cutTensor_vectorTensorAt, ← cutTensor_vectorTensorAt]
  · simpa only [cutVector, Units.smul_def, neg_mul_neg, ← Nat.cast_mul,
      Int.coe_negOnePow_natCast] using! H
  · rw [degreeSum_eq_sum, outputDegree_sum]
  · rw [degreeSum_eq_sum, outputDegree_sum]

/-- C340：同じ切断係数を掛けた項の隣接交換の等式（BF §2.2.4–6）。 -/
lemma cutTerm_adjacent {m q n : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word (n + 1) (m + 1)) (a : Fin n) (x : S _⦋q⦌) :
    (permutationAction (chains A S) (n + 1) (adjacentTransposition a)).asIso.hom.f
        (-((m + q + 1 - (n + 1) : ℕ) : ℤ)) (cutTerm A S s v x) =
      cutTerm A S s (Surjection.Word.rename (adjacentTransposition a) v) x := by
  rw [permutationAction_adjacent]
  change (adjacentIso (chains A S) n a).hom.f (-((m + q + 1 - (n + 1) : ℕ) : ℤ))
    (cutTerm A S s v x) = _
  unfold cutTerm
  rw [map_zsmul, cutTensorAt_adjacent,
    smul_smul, ← cutSign_adjacent]
  rfl

/-- C341：同じ切断項の任意の色置換は、元の実テンソルの置換に一致（BF §2.2.6）。 -/
lemma cutTerm_permutation {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (σ : Equiv.Perm (Fin r)) (x : S _⦋q⦌) :
    (permutationAction (chains A S) r σ).asIso.hom.f
        (-((m + q + 1 - r : ℕ) : ℤ)) (cutTerm A S s v x) =
      cutTerm A S s (Surjection.Word.rename σ v) x := by
  cases r with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp only [permutationAction_one, HomologicalComplex.id_f, ModuleCat.id_apply,
      Surjection.Word.rename_one]
  | succ n =>
    have H : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ v : Surjection.Word (n + 1) (m + 1),
        (permutationAction (chains A S) (n + 1) σ).asIso.hom.f
            (-((m + q + 1 - (n + 1) : ℕ) : ℤ)) (cutTerm A S s v x) =
          cutTerm A S s (Surjection.Word.rename σ v) x := by
      intro τ
      apply permutation_induction_right τ
      · intro w
        simp only [permutationAction_one, HomologicalComplex.id_f, ModuleCat.id_apply,
          Surjection.Word.rename_one]
      · intro ρ a hρ w
        rw [permutationAction_mul, Surjection.Word.rename_mul]
        change (permutationAction (chains A S) (n + 1) ρ).asIso.hom.f _
          ((permutationAction (chains A S) (n + 1) (adjacentTransposition a)).asIso.hom.f _
            (cutTerm A S s w x)) = _
        rw [cutTerm_adjacent]
        exact hρ _
    exact H σ v

end SerrePositivity.EInfinity.SimplexCuts
