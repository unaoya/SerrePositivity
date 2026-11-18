module

public import SerrePositivity.HomologicalAlgebra.Complexes.NatTensor.Homogeneous
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# 四重自然数鎖テンソルからの射の外延性

概要：Berger–Fresse §1.1.4 の四因子比較を各斉次包含で検査する。
方針：余積の普遍性を外側と二つの内側の全次数へ順に適用する。
規約：任意の自然数鎖複体と任意の係数加群を扱う。
使われ方：負次数比較と四因子交換の適合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NatTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

private lemma source_whiskerRight_ext (P Q : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (T Y : ModuleCat.{u} A) {f g : (_root_.SerrePositivity.NatTensor.tensor P Q).X n ⊗ T ⟶ Y}
    (h : ∀ i j (hij : i + j = n), (ιTensorObj P Q i j n hij ▷ T) ≫ f =
      (ιTensorObj P Q i j n hij ▷ T) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorRight T) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

private lemma source_whiskerLeft_ext (P Q : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (T Y : ModuleCat.{u} A) {f g : T ⊗ (_root_.SerrePositivity.NatTensor.tensor P Q).X n ⟶ Y}
    (h : ∀ i j (hij : i + j = n), (T ◁ ιTensorObj P Q i j n hij) ≫ f =
      (T ◁ ιTensorObj P Q i j n hij) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft T) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

/-- 概要：四重テンソルからの射は全四次数の包含上で決まる（BF §1.1.4）。
方針：外側の全次数と二つの内側の全次数に余積の外延性を適用する。
規約：括弧付けは左二因子と右二因子に揃える。
使われ方：四因子の負次数比較の可換性を純テンソルで証明する。 -/
lemma quad_hom_ext (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) {Y : ModuleCat.{u} A} {f g : (_root_.SerrePositivity.NatTensor.tensor (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U)).X n ⟶ Y}
    (h : ∀ i j k l (hijkl : i + j + k + l = n),
      _root_.SerrePositivity.NatTensor.tensorQuadι P Q T U i j k l n hijkl ≫ f =
        _root_.SerrePositivity.NatTensor.tensorQuadι P Q T U i j k l n hijkl ≫ g) : f = g := by
  apply mapBifunctor.hom_ext
  intro a b hab
  change a + b = n at hab
  apply _root_.SerrePositivity.NatTensor.source_whiskerRight_ext P Q a ((_root_.SerrePositivity.NatTensor.tensor T U).X b) Y
  intro i j hij
  apply _root_.SerrePositivity.NatTensor.source_whiskerLeft_ext T U b (P.X i ⊗ Q.X j) Y
  intro k l hkl
  subst a
  subst b
  simp only [← tensorHom_def'_assoc]
  exact h i j k l (by omega)

end SerrePositivity.NatTensor
