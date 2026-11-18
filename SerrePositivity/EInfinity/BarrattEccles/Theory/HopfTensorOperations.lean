module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HopfComponents
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEquivariantEvaluation

/-!
# Hopf 対角によるテンソル上の演算

## 概要
Berger–Fresse §1.1.4 の対角から、HA 3.2.4.7 の比較先のテンソル演算を作る。

## 方針
係数を Hopf 対角で分け、入力のテンソル冪を二列に分けて各代数の作用を適用する。

## 規約
零入力を含み、Koszul 符号は既存の対称モノイダル構造のものを使う。

## 使われ方
二項余積から台のテンソルへの自然な比較と、その代数構造の証明の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- BF §1.1.4 の零入力の分離の指定射。 -/
lemma tensorPowerSeparation_zero_hom (V W : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W 0).hom = (λ_ (𝟙_ (Complex A))).inv := rfl

/-- BF §1.1.4 の分離の後続段での指定射。 -/
lemma tensorPowerSeparation_succ_hom (V W : Complex A) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 1)).hom =
      ((V ⊗ W) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom) ≫
        tensorμ V W (power V n) (power W n) := rfl

/-- BF §1.1.4 の対角で係数と入力を分けて得るテンソル上の演算。 -/
def hopfTensorAction (hP : P.Hopf) (X Y : P.Algebra) (n : ℕ) :
    P.arity n ⊗ power (X.carrier ⊗ Y.carrier) n ⟶ X.carrier ⊗ Y.carrier :=
  (hP.diagonalComponent n ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation X.carrier Y.carrier n).hom) ≫
    tensorμ _ _ _ _ ≫ (X.action n ⊗ₘ Y.action n)

/-- BF §1.1.4 の係数と入力の同時置換はテンソル演算を保つ。 -/
lemma hopfTensorAction_equivariance (hP : P.Hopf) (X Y : P.Algebra)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction (X.carrier ⊗ Y.carrier) n σ).asIso.hom) ≫
      hopfTensorAction hP X Y n = hopfTensorAction hP X Y n := by
  have hd : P.sequence.map (FiniteBijection.permutation n σ) ≫ hP.diagonalComponent n =
      hP.diagonalComponent n ≫
        (P.sequence.map (FiniteBijection.permutation n σ) ⊗ₘ
          P.sequence.map (FiniteBijection.permutation n σ)) :=
    hP.diagonal.map.naturality (FiniteBijection.permutation n σ)
  unfold hopfTensorAction
  rw [tensorHom_comp_tensorHom_assoc, hd, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_permutation,
    ← tensorHom_comp_tensorHom_assoc]
  erw [tensorμ_natural_assoc]
  rw [tensorHom_comp_tensorHom, X.equivariance, Y.equivariance]

end SerrePositivity.EInfinity
