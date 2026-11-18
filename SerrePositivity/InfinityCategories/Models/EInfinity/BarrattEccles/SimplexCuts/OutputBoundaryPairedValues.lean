module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryValues

/-!
模型。文献の定義との比較は後で
# 色と面番号の組を保つ全出力境界値

Berger–Fresse §2.2.7、M14 L09a。
元の出力値を、逆同値の依存した色・面番号の組を保って読む。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C225：同じ実出力値を、逆同値の色と面番号を分離せずに評価する。 -/
lemma universalBoundaryValue_output_paired (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun n : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X n) h)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w)
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w)).symm k).1
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w)).symm k).2 x) := rfl

/-- C225の証明分割：同じ依存した組の等式を、実境界値全体へ写す。 -/
lemma universalBoundaryValue_output_of_pair (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1)
    (ij : Σ a : Fin (r + 1), Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) a + 1))
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w)).symm k = ij) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun n : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X n) h)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) ij.1 ij.2 x) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_output_paired A S w q x s k h
  exact ht.trans (congrArg (fun p : Σ a : Fin (r + 1),
      Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) a + 1) =>
    (eqToHom (congrArg (fun n : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X n) h)).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) p.1 p.2 x)) hp)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
