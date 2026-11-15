module

public import SerrePositivity.EInfinity.SimplexCuts.CochainAction
public import SerrePositivity.EInfinity.SimplexCuts.CutSumVectorExpansion

/-!
# 元のcochainActionの基底語と生成元での実際の値

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §299。
同じ生成元と斉次テンソルを、元の等式移送と同じ複体射で読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元の複体射を基底語と正規化生成元で評価した値は同じ切断和（BF §2.2.6）。 -/
lemma cochainAction_basis_generator (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (cochainAction A S (r + 1)).f (-((d + q : ℕ) : ℤ))
      (ιTensorObj (Surjection.complex A (r + 1)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-((d + q : ℕ) : ℤ)) (by omega)
        ((Surjection.complexXIso A (r + 1) d).inv
          (Surjection.basis A (r + 1) d (ULift.up u)) ⊗ₜ[A] gen A S q x)) =
      cutSum A S u x := by
  change (ιTensorObj (Surjection.complex A (r + 1)) (chains A S)
    (-(d : ℤ)) (-(q : ℤ)) (-((d + q : ℕ) : ℤ)) (by omega) ≫
      (cochainAction A S (r + 1)).f _).hom _ = _
  rw [ι_cochainAction]
  change positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
    (-((d + q : ℕ) : ℤ)) (by omega) _ _ = _
  rw [positiveIntegerBilinear_neg]
  exact positiveComponent_generator A S u x

end SerrePositivity.EInfinity.SimplexCuts
