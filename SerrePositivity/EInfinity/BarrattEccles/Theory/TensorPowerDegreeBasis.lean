module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeBasis

/-!
# 反復テンソルの次数付き基底と入力の語

## 概要
Berger–Moerdijk §1 の Schur 表示で、反復テンソルの基底の入力を記録する。

## 方針
双次数の余積基底を帰納的に使い、各基底ベクトルに入力の有限列を対応させる。

## 規約
零回のテンソルは単位、入力の列は空列。

## 使われ方
セル代数の基底に付ける入力の重み。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct

variable {A : Type u} [CommRing A]

/-- A basis for a tensor degree, retaining the two specified basis indices. -/
def tensorGradedBasis {K L : Complex A} {I J : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (c : ∀ i, Module.Basis (J i) A (L.X i))
    (i : ℤ) :
    Module.Basis (Σ a : {a : ℤ × ℤ // a.1 + a.2 = i}, I a.1.1 × J a.1.2) A
      ((K ⊗ L).X i) :=
  (moduleCoproductBasis (cochainTensorSummand K L i)
    (fun a => (b a.1.1).tensorProduct (c a.1.2))).map
      (cochainTensorXIso K L i).symm.toLinearEquiv

/-- A tensor-degree basis vector is the specified inclusion of a pure tensor. -/
lemma tensorGradedBasis_apply {K L : Complex A} {I J : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (c : ∀ i, Module.Basis (J i) A (L.X i))
    (i : ℤ) (a : Σ a : {a : ℤ × ℤ // a.1 + a.2 = i}, I a.1.1 × J a.1.2) :
    tensorGradedBasis b c i a =
      ιTensorObj K L a.1.1.1 a.1.1.2 i a.1.2
        (b a.1.1.1 a.2.1 ⊗ₜ[A] c a.1.1.2 a.2.2) := by
  classical
  rw [tensorGradedBasis, Module.Basis.map_apply, moduleCoproductBasis_apply]
  erw [Module.Basis.tensorProduct_apply' (b a.1.1.1) (c a.1.1.2) a.2]
  rfl

/-- The index for the basis of the tensor unit in a given degree. -/
def unitDegreeIndex (i : ℤ) : Type u :=
  if i = 0 then ULift.{u} PUnit else PEmpty

/-- The tensor unit has its usual basis in degree zero and the empty basis elsewhere. -/
def unitDegreeBasis (i : ℤ) :
    Module.Basis (unitDegreeIndex i) A ((𝟙_ (Complex A)).X i) := by
  classical
  by_cases h : i = 0
  · subst i
    change Module.Basis (ULift.{u} PUnit) A _
    exact (Module.Basis.singleton (ULift.{u} PUnit) A).map
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).symm.toLinearEquiv
  · haveI : Subsingleton ((𝟙_ (Complex A)).X i) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) i h)
    change Module.Basis (if i = 0 then ULift.{u} PUnit else PEmpty) A _
    rw [ite_eq_right h]
    exact Module.Basis.empty _

/-- The recursively specified indices for the right-associated tensor power. -/
def powerGradedIndex (I : ℤ → Type u) : ℕ → ℤ → Type u
  | 0, i => unitDegreeIndex i
  | n + 1, i => Σ a : {a : ℤ × ℤ // a.1 + a.2 = i}, I a.1.1 × powerGradedIndex I n a.1.2

/-- A basis for each degree of the actual tensor power. -/
def powerGradedBasis {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) :
    ∀ n i, Module.Basis (powerGradedIndex I n i) A ((TensorPowers.power K n).X i)
  | 0, i => unitDegreeBasis i
  | n + 1, i => tensorGradedBasis b (powerGradedBasis b n) i

/-- The finite list of homogeneous inputs underlying a tensor-power basis index. -/
def powerGradedInputs {I : ℤ → Type u} :
    ∀ n i, powerGradedIndex I n i → List (Σ i, I i)
  | 0, _, _ => []
  | n + 1, _, ⟨a, x, y⟩ => ⟨a.1.1, x⟩ :: powerGradedInputs n a.1.2 y

lemma powerGradedInputs_length {I : ℤ → Type u} (n : ℕ) (i : ℤ)
    (x : powerGradedIndex I n i) : (powerGradedInputs n i x).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    obtain ⟨a, x, y⟩ := x
    exact congrArg Nat.succ (ih a.1.2 y)

/-- The tensor degree equals the sum of the degrees of its specified inputs. -/
lemma powerGradedInputs_degree {I : ℤ → Type u} (n : ℕ) (i : ℤ)
    (x : powerGradedIndex I n i) :
    ((powerGradedInputs n i x).map Sigma.fst).sum = i := by
  classical
  induction n generalizing i with
  | zero =>
    by_cases h : i = 0
    · subst i
      rfl
    · change (if i = 0 then ULift.{u} PUnit else PEmpty) at x
      rw [ite_eq_right h] at x
      exact x.elim
  | succ n ih =>
    obtain ⟨a, x, y⟩ := x
    change a.1.1 + ((powerGradedInputs n a.1.2 y).map Sigma.fst).sum = i
    rw [ih a.1.2 y]
    exact a.2

/-- The sum of the weights of the specified inputs, counting repetitions. -/
def powerGradedWeight {I : ℤ → Type u} (w : (Σ i, I i) → ℕ)
    (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) : ℕ :=
  ((powerGradedInputs n i x).map w).sum

/-- An input weight dominating its degree also dominates the degree of every tensor word. -/
lemma degree_le_powerGradedWeight {I : ℤ → Type u} (w : (Σ i, I i) → ℕ)
    (hw : ∀ x, x.1 ≤ (w x : ℤ)) (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) :
    i ≤ (powerGradedWeight w n i x : ℤ) := by
  classical
  induction n generalizing i with
  | zero =>
    by_cases h : i = 0
    · subst i
      exact le_refl 0
    · change (if i = 0 then ULift.{u} PUnit else PEmpty) at x
      rw [ite_eq_right h] at x
      exact x.elim
  | succ n ih =>
    obtain ⟨a, x, y⟩ := x
    have h₁ := hw ⟨a.1.1, x⟩
    change a.1.1 ≤ (w ⟨a.1.1, x⟩ : ℤ) at h₁
    have h₂ := ih a.1.2 y
    change i ≤ ((w ⟨a.1.1, x⟩ + powerGradedWeight w n a.1.2 y : ℕ) : ℤ)
    have h := a.2
    omega

end SerrePositivity.EInfinity
