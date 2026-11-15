module

public import SerrePositivity.EInfinity.SimplexCuts.UnaryCutFaces
public import SerrePositivity.EInfinity.SimplexCuts.CutSumVectorExpansion
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.EInfinity.Surjection.CompositionUnit

/-!
# 一文字単位の全入力次数のBF切断和

Berger–Fresse §2.2.6、M14 L13、報告 §384。
元の唯一Cutを評価し、一般の複体の同じ右単位子の逆へ比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 一因子の同じ斉次テンソルは指定次数の右単位子の逆（BF §2.2.6）。 -/
lemma vectorTensorAt_one (A : Type u) [CommRing A] (K : Complex A)
    (a : Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ) (h : -(a.1 : ℤ) = t) :
    vectorTensorAt K 1 (fun _ => a) t (by simp [vectorDegree, degreeSum]; omega) =
      (oneIso K).inv.f t ((eqToHom (congrArg K.X h)).hom a.2) := by
  rw [vectorTensorAt_succ K 0 _ t 0 t h (by rfl) (add_zero t)]
  change ιTensorObj K (𝟙_ (Complex A)) t 0 t (add_zero t)
    ((eqToHom (congrArg K.X h)).hom a.2 ⊗ₜ[A]
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
  exact (BarrattEccles.cochain_rightUnitor_inv_apply A K t _).symm

/-- L13：一般次元の元の一文字単位Cut和は右単位子の逆（BF §2.2.6）。 -/
lemma cutSum_unit (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ} (x : S _⦋q⦌) :
    cutSum A S (Surjection.permutationWord (1 : Equiv.Perm (Fin 1))) x =
      (oneIso (chains A S)).inv.f (-((0 + q : ℕ) : ℤ))
        ((eqToHom (congrArg (chains A S).X
          (by omega : -(q : ℤ) = -((0 + q : ℕ) : ℤ)))).hom (gen A S q x)) := by
  let u := Surjection.permutationWord (1 : Equiv.Perm (Fin 1))
  let s : Cut 0 q := ⟨∅, rfl⟩
  have hunique (t : Cut 0 q) : t = s := Subtype.ext (Finset.card_eq_zero.mp t.property)
  rw [cutSum_eq_sum_vectorTensorAt]
  rw [Finset.sum_eq_single s]
  · rw [unaryCut_sign s (positiveWord u), one_smul]
    let f := cutGeneratorFamily A S s (positiveWord u) x
    have ht : -(vectorDegree (chains A S) 1 f : ℤ) = -((0 + q : ℕ) : ℤ) := by
      rw [vectorDegree_cutGeneratorFamily]
      omega
    have hg : -(vectorDegree (chains A S) 1
        (fun _ => (⟨q, gen A S q x⟩ : Σ d : ℕ, (chains A S).X (-(d : ℤ)))) : ℤ) =
        -((0 + q : ℕ) : ℤ) := by simp [vectorDegree, degreeSum]
    have H := vectorTensorAt_congr (chains A S) 1 f
      (fun _ => ⟨q, gen A S q x⟩) (-((0 + q : ℕ) : ℤ)) ht hg
      (unaryCut_generatorFamily A S s (positiveWord u) x)
    exact H.trans (vectorTensorAt_one A (chains A S) ⟨q, gen A S q x⟩
      (-((0 + q : ℕ) : ℤ)) (by dsimp; omega))
  · intro t _ hts
    exact False.elim (hts (hunique t))
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

end SerrePositivity.EInfinity.SimplexCuts
