module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCoefficientAction
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.BinaryInput

/-!
# E 代数の演算は入力置換で鎖ホモトピック

概要：BF §1 の E(n) の可縮性と代数の等変性から、入力置換による作用のホモトピーを得る。
方針：置換された係数と恒等係数を augmentation で比較し、作用へ移す。
規約：任意の可換環、全 arity と全置換。
使われ方：H⁰ の二項積の可換性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

attribute [local implicit_reducible] TensorPowers.power

variable {A : Type u} [CommRing A]

/-- 概要：E(n) の置換作用は恒等射と鎖ホモトピック（BF §1）。
方針：augmentation の自然性と Com の自明な置換作用を使う。
規約：同変な収縮を仮定しない。
使われ方：代数の入力置換のホモトピー。 -/
def permutationHomotopy (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Homotopy ((operad A).sequence.map (FiniteBijection.permutation n σ))
      (𝟙 ((operad A).arity n)) :=
  coefficientHomotopy A n _ _ (by
    exact ((augmentation A).map.naturality (FiniteBijection.permutation n σ)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- 概要：E 代数の全入力置換による演算は元の演算とホモトピック（BF §1）。
方針：係数置換のホモトピーを入力置換とテンソルし、代数の等変性を使う。
規約：零入力も含む実際の複体射の鎖ホモトピー。
使われ方：二項積の交換を H⁰ の等式に移す。 -/
def actionPermutationHomotopy (X : (operad A).Algebra) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Homotopy (X.action n)
      (((operad A).arity n ◁ (permutationAction X.carrier n σ).asIso.hom) ≫ X.action n) := by
  have ht := SerrePositivity.cochainTensorHomotopyLeft (permutationHomotopy n σ)
    (permutationAction X.carrier n σ).asIso.hom
  change Homotopy
    ((operad A).sequence.map (FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction X.carrier n σ).asIso.hom)
    (𝟙 ((operad A).arity n) ⊗ₘ (permutationAction X.carrier n σ).asIso.hom) at ht
  have h := ht.compRight (X.action n)
  have hr : (𝟙 ((operad A).arity n) ⊗ₘ (permutationAction X.carrier n σ).asIso.hom) ≫
      X.action n = ((operad A).arity n ◁
        (permutationAction X.carrier n σ).asIso.hom) ≫ X.action n :=
    congrArg (fun k => k ≫ X.action n) (id_tensorHom _ _)
  exact (Homotopy.ofEq (X.equivariance n σ).symm).trans (h.trans (Homotopy.ofEq hr))

/-- 概要：E 代数から取り出した二項積は交換した積と鎖ホモトピック（BF §1）。
方針：全入力の置換ホモトピーへ arity 2 の係数と単位因子の挿入を前合成する。
規約：実際の Koszul 交換を使う。
使われ方：H⁰ の積の可換性。 -/
def homologyBinaryCommutativityHomotopy (X : (operad A).Algebra) :
    Homotopy (homologyBinary X) ((β_ X.carrier X.carrier).hom ≫ homologyBinary X) := by
  have h := (actionPermutationHomotopy X 2
    (Coxeter.adjacentTransposition (0 : Fin 1))).compLeft
      ((X.carrier ◁ (oneIso X.carrier).inv) ≫ (λ_ (power X.carrier 2)).inv ≫
        (aritySection A 2 ▷ power X.carrier 2))
  simp only [Category.assoc] at h
  rw [← whisker_exchange_assoc] at h
  have hn := (leftUnitor_inv_naturality
    (permutationAction X.carrier 2 (Coxeter.adjacentTransposition (0 : Fin 1))).asIso.hom).symm
  rw [reassoc_of% hn, reassoc_of% (_root_.SerrePositivity.HomologyZero.binaryInput_braiding X.carrier).symm] at h
  simpa only [homologyBinary, homologyOperation, Category.assoc] using h

end SerrePositivity.EInfinity.BarrattEccles
