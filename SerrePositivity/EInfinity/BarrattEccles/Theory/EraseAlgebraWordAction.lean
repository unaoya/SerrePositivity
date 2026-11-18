module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ErasePowerComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseFreeGenerators
public import SerrePositivity.EInfinity.BarrattEccles.Theory.PowerWordNaturality

/-!
# 微分を消した代数での指定入力の演算

## 概要
Berger–Moerdijk §1 の代数の演算を、微分を消す比較と指定された語の基底上で照合する。

## 方針
テンソル冪の比較が基底を保つ式と、代数の射の作用保存を斉次元で評価する。

## 規約
比較は次数ごとの元の等式であり、微分を消す前の複体同型は仮定しない。

## 使われ方
実際のセル段と自由代数の作用の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- Erasing the differential preserves the evaluation of every specified homogeneous word. -/
lemma eraseAlgebra_action_basis (X : P.Algebra) {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (X.carrier.X i))
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    ((P.eraseAlgebra.obj X).action n).f i
      (ιTensorObj (P.erase.arity n) (power ((eraseDifferential A).obj X.carrier) n)
        p r i h (u ⊗ₜ[A]
          powerGradedBasis (K := (eraseDifferential A).obj X.carrier) b n r x)) =
    (X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerGradedBasis b n r x)) := by
  change (X.action n).f i
    ((eraseDifferentialTensorIso A (P.arity n) (power X.carrier n)).hom.f i
      ((cochainTensorMap (𝟙 ((eraseDifferential A).obj (P.arity n)))
        (laxPowerComparison (eraseDifferential A) X.carrier n)).f i
        (ιTensorObj ((eraseDifferential A).obj (P.arity n))
          (power ((eraseDifferential A).obj X.carrier) n) p r i h
          (u ⊗ₜ[A]
            powerGradedBasis (K := (eraseDifferential A).obj X.carrier) b n r x)))) = _
  rw [eraseDifferentialTensorIso_hom_f]
  erw [cochainTensorMap_apply_ι]
  rw [eraseDifferentialPower_hom_basis]
  rfl

/-- A map of algebras carries the action on specified inputs to the action on their images. -/
lemma action_basis_naturality {X Y : P.Algebra} (f : X ⟶ Y) {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (X.carrier.X i))
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    f.hom.f i ((X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerGradedBasis b n r x))) =
    (Y.action n).f i (ιTensorObj (P.arity n) (power Y.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue Y.carrier (fun i z => f.hom.f i (b i z)) n r x)) := by
  have hc := congrArg (fun z => z.f i
    (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerGradedBasis b n r x))) (f.comm n)
  change f.hom.f i ((X.action n).f i _) =
    (Y.action n).f i ((cochainTensorMap (𝟙 (P.arity n)) (TensorPowers.map f.hom n)).f i
      (ιTensorObj (P.arity n) (power X.carrier n) p r i h
        (u ⊗ₜ[A] powerGradedBasis b n r x))) at hc
  rw [cochainTensorMap_apply_ι] at hc
  have hp := powerWordValue_naturality f.hom (fun i z => b i z) n r x
  rw [powerWordValue_basis] at hp
  rw [hp] at hc
  exact hc

/-- An isomorphism after erasure identifies actions on the corresponding original bases. -/
lemma erasedIso_action_basis {X Y : P.Algebra}
    (e : P.eraseAlgebra.obj X ≅ P.eraseAlgebra.obj Y) {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (X.carrier.X i))
    (c : ∀ i, Module.Basis (I i) A (Y.carrier.X i))
    (he : ∀ i z, e.hom.hom.f i (b i z) = c i z)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    e.hom.hom.f i ((X.action n).f i
      (ιTensorObj (P.arity n) (power X.carrier n) p r i h
        (u ⊗ₜ[A] powerGradedBasis b n r x))) =
    (Y.action n).f i (ιTensorObj (P.arity n) (power Y.carrier n) p r i h
      (u ⊗ₜ[A] powerGradedBasis c n r x)) := by
  have hc := action_basis_naturality e.hom
    (fun i => (show Module.Basis (I i) A
      (((eraseDifferential A).obj X.carrier).X i) from b i)) n p r i h u x
  erw [eraseAlgebra_action_basis X b n p r i h u x] at hc
  have hh : (fun i z => e.hom.hom.f i (b i z)) = (fun i z => c i z) := by
    funext i z
    exact he i z
  erw [hh, powerWordValue_basis, eraseAlgebra_action_basis Y c n p r i h u x] at hc
  exact hc

end SerrePositivity.EInfinity.Operad
