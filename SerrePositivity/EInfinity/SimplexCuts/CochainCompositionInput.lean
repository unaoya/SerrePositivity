module

public import SerrePositivity.EInfinity.SimplexCuts.SimplexTripleGeneratorExt
public import SerrePositivity.EInfinity.SimplexCuts.CochainCompositionBasisAll
public import SerrePositivity.EInfinity.Surjection.ComplexComposition

/-!
# 元の部分合成射の実際の二語・単体入力

Berger–Fresse §1.2.4・§2.2.6、M14 L14/L16、報告 §388。
同じ複体射の負次数成分を元のcompositionOnWordsへ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じ二語・単体入力で部分合成射の左辺を評価する（BF §2.2.6）。 -/
lemma cochainAction_composition_input (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    ((Surjection.complexPartialComposition A m n k ▷ chains A S) ≫
      cochainAction A S (m + n)).f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ))
        (wordPairSimplexInput A S u v x) =
    (cochainAction A S (m + n)).f (-(d : ℤ) + -(e : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A (m + n)) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(e : ℤ) + -(q : ℤ)) (by omega)
        ((Surjection.complexXIso A (m + n) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) := by
  let z : ℤ := -(d : ℤ) + -(e : ℤ) + -(q : ℤ)
  have reindex (a : ℤ) (ha : -((d + e : ℕ) : ℤ) = a)
      (hab : -(d : ℤ) + -(e : ℤ) = a) (haz : a + -(q : ℤ) = z) :
      ((Surjection.complexPartialComposition A m n k ▷ chains A S) ≫
        cochainAction A S (m + n)).f z
        (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) (chains A S)
          a (-(q : ℤ)) z haz
          (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A n)
            (-(d : ℤ)) (-(e : ℤ)) a hab
            ((Surjection.complexXIso A (m + 1) d).inv
                (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A n e).inv (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A]
            gen A S q x)) =
      (cochainAction A S (m + n)).f z
        (ιTensorObj (Surjection.complex A (m + n)) (chains A S)
          (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) z (by dsimp only [z]; omega)
          ((Surjection.complexXIso A (m + n) (d + e)).inv
            (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) := by
    subst ha
    change (cochainAction A S (m + n)).f z
      (((Surjection.complexPartialComposition A m n k) ▷ chains A S).f z _) = _
    rw [SerrePositivity.DifferentialGraded.whiskerRight_apply,
      Surjection.complexPartialComposition_neg_tmul]
    simp only [ModuleCat.hom_inv_apply, Surjection.partialComposition_basis]
  exact reindex (-(d : ℤ) + -(e : ℤ)) (by omega) rfl rfl

end SerrePositivity.EInfinity.SimplexCuts
