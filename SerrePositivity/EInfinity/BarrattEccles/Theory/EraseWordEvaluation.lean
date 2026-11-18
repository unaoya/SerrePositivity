module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAlgebraWordAction

/-!
# 微分を消す比較と任意の指定入力の語

## 概要
Berger–Moerdijk §1 の演算の語を、基底とは限らない斉次入力で比較する。

## 方針
テンソル冪の比較の帰納法と、代数の射の作用保存を適用する。

## 規約
入力は任意の指定された斉次元で、微分が零である必要はない。

## 使われ方
自由代数の生成元の像で、実際のセル段の基底語を評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- The strong power comparison preserves every word of specified homogeneous inputs. -/
lemma eraseDifferentialPower_hom_value (K : Complex A) {I : ℤ → Type u}
    (g : ∀ i, I i → K.X i) (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) :
    (laxPowerComparison (eraseDifferential A) K n).f i
      (powerWordValue ((eraseDifferential A).obj K) g n i x) =
      powerWordValue K g n i x := by
  induction n generalizing i with
  | zero =>
    change (eraseDifferentialUnitIso A).hom.f i (unitDegreeBasis (A := A) i x) = _
    rw [eraseDifferentialUnitIso_hom_f]
    rfl
  | succ n ih =>
    obtain ⟨a, z, y⟩ := x
    change (eraseDifferentialTensorIso A K (power K n)).hom.f i
      ((cochainTensorMap (𝟙 ((eraseDifferential A).obj K))
        (laxPowerComparison (eraseDifferential A) K n)).f i
        (ιTensorObj ((eraseDifferential A).obj K) (power ((eraseDifferential A).obj K) n)
          a.1.1 a.1.2 i a.2
          (g a.1.1 z ⊗ₜ[A] powerWordValue ((eraseDifferential A).obj K) g n a.1.2 y))) = _
    rw [eraseDifferentialTensorIso_hom_f]
    change (cochainTensorMap (𝟙 ((eraseDifferential A).obj K))
      (laxPowerComparison (eraseDifferential A) K n)).f i
      (ιTensorObj ((eraseDifferential A).obj K) (power ((eraseDifferential A).obj K) n)
        a.1.1 a.1.2 i a.2
        (g a.1.1 z ⊗ₜ[A] powerWordValue ((eraseDifferential A).obj K) g n a.1.2 y)) = _
    rw [cochainTensorMap_apply_ι, ih]
    rfl

namespace Operad
variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- Erasing the differential preserves an operation on arbitrary specified homogeneous inputs. -/
lemma eraseAlgebra_action_value (X : P.Algebra) {I : ℤ → Type u}
    (g : ∀ i, I i → X.carrier.X i)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    ((P.eraseAlgebra.obj X).action n).f i
      (ιTensorObj (P.erase.arity n) (power ((eraseDifferential A).obj X.carrier) n)
        p r i h (u ⊗ₜ[A] powerWordValue ((eraseDifferential A).obj X.carrier) g n r x)) =
    (X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue X.carrier g n r x)) := by
  change (X.action n).f i
    ((eraseDifferentialTensorIso A (P.arity n) (power X.carrier n)).hom.f i
      ((cochainTensorMap (𝟙 ((eraseDifferential A).obj (P.arity n)))
        (laxPowerComparison (eraseDifferential A) X.carrier n)).f i
        (ιTensorObj ((eraseDifferential A).obj (P.arity n))
          (power ((eraseDifferential A).obj X.carrier) n) p r i h
          (u ⊗ₜ[A] powerWordValue ((eraseDifferential A).obj X.carrier) g n r x)))) = _
  rw [eraseDifferentialTensorIso_hom_f]
  erw [cochainTensorMap_apply_ι]
  rw [eraseDifferentialPower_hom_value]
  rfl

/-- A map of algebras preserves operations on arbitrary words of homogeneous inputs. -/
lemma action_value_naturality {X Y : P.Algebra} (f : X ⟶ Y) {I : ℤ → Type u}
    (g : ∀ i, I i → X.carrier.X i)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    f.hom.f i ((X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue X.carrier g n r x))) =
    (Y.action n).f i (ιTensorObj (P.arity n) (power Y.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue Y.carrier (fun i z => f.hom.f i (g i z)) n r x)) := by
  have hc := congrArg (fun z => z.f i
    (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue X.carrier g n r x))) (f.comm n)
  change f.hom.f i ((X.action n).f i _) =
    (Y.action n).f i ((cochainTensorMap (𝟙 (P.arity n)) (TensorPowers.map f.hom n)).f i
      (ιTensorObj (P.arity n) (power X.carrier n) p r i h
        (u ⊗ₜ[A] powerWordValue X.carrier g n r x))) at hc
  rw [cochainTensorMap_apply_ι, powerWordValue_naturality] at hc
  exact hc

/-- An isomorphism after erasure preserves operations on arbitrary specified input words. -/
lemma erasedIso_action_value {X Y : P.Algebra}
    (e : P.eraseAlgebra.obj X ≅ P.eraseAlgebra.obj Y) {I : ℤ → Type u}
    (g : ∀ i, I i → X.carrier.X i)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    e.hom.hom.f i ((X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue X.carrier g n r x))) =
    (Y.action n).f i (ιTensorObj (P.arity n) (power Y.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue Y.carrier (fun i z => e.hom.hom.f i (g i z)) n r x)) := by
  have hc := action_value_naturality e.hom g n p r i h u x
  erw [eraseAlgebra_action_value X g n p r i h u x,
    eraseAlgebra_action_value Y (fun i z => e.hom.hom.f i (g i z)) n p r i h u x] at hc
  exact hc

end Operad
end SerrePositivity.EInfinity
