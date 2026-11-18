module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UnaryCutFaces
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutSumVectorExpansion
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionUnit

/-!
模型。文献の定義との比較は後で
# 一文字単位の全入力次数のBF切断和

Berger–Fresse §2.2.6、M14 L13、報告 §384。
元の唯一Cutを評価し、一般の複体の同じ右単位子の逆へ比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 一因子の同じ斉次テンソルは指定次数の右単位子の逆（BF §2.2.6）。 -/
lemma vectorTensorAt_one (A : Type u) [CommRing A] (K : Complex A)
    (a : Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ) (h : -(a.1 : ℤ) = t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K 1 (fun _ => a) t (by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum]; omega) =
      (oneIso K).inv.f t ((eqToHom (congrArg K.X h)).hom a.2) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_succ K 0 _ t 0 t h (by rfl) (add_zero t)]
  change ιTensorObj K (𝟙_ (Complex A)) t 0 t (add_zero t)
    ((eqToHom (congrArg K.X h)).hom a.2 ⊗ₜ[A]
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.cochain_rightUnitor_inv_apply A K t _).symm

/-- L13：一般次元の元の一文字単位Cut和は右単位子の逆（BF §2.2.6）。 -/
lemma cutSum_unit (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ} (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))) x =
      (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)).inv.f (-((0 + q : ℕ) : ℤ))
        ((eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X
          (by omega : -(q : ℤ) = -((0 + q : ℕ) : ℤ)))).hom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) := by
  let u := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))
  let s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut 0 q := ⟨∅, rfl⟩
  have hunique (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut 0 q) : t = s := Subtype.ext (Finset.card_eq_zero.mp t.property)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_eq_sum_vectorTensorAt]
  rw [Finset.sum_eq_single s]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.unaryCut_sign s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u), one_smul]
    let f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) x
    have ht : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 1 f : ℤ) = -((0 + q : ℕ) : ℤ) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cutGeneratorFamily]
      omega
    have hg : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 1
        (fun _ => (⟨q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x⟩ : Σ d : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(d : ℤ)))) : ℤ) =
        -((0 + q : ℕ) : ℤ) := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum]
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_congr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 1 f
      (fun _ => ⟨q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x⟩) (-((0 + q : ℕ) : ℤ)) ht hg
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.unaryCut_generatorFamily A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) x)
    exact H.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_one A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ⟨q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x⟩
      (-((0 + q : ℕ) : ℤ)) (by dsimp; omega))
  · intro t _ hts
    exact False.elim (hts (hunique t))
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
