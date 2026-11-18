module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.Classes
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# 零次集中複体の元の成分と実 H⁰ の線形同型

概要：零次集中複体の零次成分を、元のホモロジー類の写像で実 H⁰ へ同定する。
方針：非負性から境界が零、非正性から全零次元が閉じていることを使う。
規約：ホモロジーの型・加群構造を置き換えない。
使われ方：元の零次 Com 代数から H⁰ の離散像への標準射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologyZero
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] (K : Complex A)

lemma classMap_injective [K.IsStrictlyGE 0] : Function.Injective (_root_.SerrePositivity.HomologyZero.classMap K) := by
  intro x y h
  have hz : _root_.SerrePositivity.HomologyZero.classMap K (x - y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨z, hz⟩ := (_root_.SerrePositivity.HomologyZero.classMap_eq_zero_iff K (x - y)).mp hz
  have : Subsingleton (K.X (-1)) :=
    (ModuleCat.isZero_iff_subsingleton).mp (K.isZero_of_isStrictlyGE 0 (-1) (by decide))
  have hzero : z = 0 := Subsingleton.elim _ _
  rw [hzero, map_zero] at hz
  apply sub_eq_zero.mp
  exact Subtype.ext hz.symm

def cyclesHomologyLinearEquiv [K.IsStrictlyGE 0] : zeroCycles K ≃ₗ[A] K.homology 0 :=
  LinearEquiv.ofBijective (_root_.SerrePositivity.HomologyZero.classMap K) ⟨_root_.SerrePositivity.HomologyZero.classMap_injective K, _root_.SerrePositivity.HomologyZero.classMap_surjective K⟩

def componentCyclesLinearEquiv [K.IsStrictlyLE 0] : K.X 0 ≃ₗ[A] zeroCycles K where
  toFun x := ⟨x, by
    have : Subsingleton (K.X 1) :=
      (ModuleCat.isZero_iff_subsingleton).mp (K.isZero_of_isStrictlyLE 0 1 (by decide))
    exact Subsingleton.elim _ _⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def componentHomologyLinearEquiv [K.IsStrictlyLE 0] [K.IsStrictlyGE 0] :
    K.X 0 ≃ₗ[A] K.homology 0 :=
  (_root_.SerrePositivity.HomologyZero.componentCyclesLinearEquiv K).trans (_root_.SerrePositivity.HomologyZero.cyclesHomologyLinearEquiv K)

end SerrePositivity.HomologyZero
