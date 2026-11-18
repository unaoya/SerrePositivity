module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalFaceTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OutputBoundaryPairedValues

/-!
模型。文献の定義との比較は後で
# BF全境界値の垂直分岐

Berger–Fresse §2.2.7、M14 L09a。
同じ入力面の指定実境界値を、既存の全垂直添字の相殺へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C252：全境界値の入力分岐は、元の同じ入力境界項。 -/
lemma universalBoundaryValue_input (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (c : Fin (q + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) (q - 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x (.inr (.inr c)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm A S w q c x := by
  rfl

/-- C253：正の入力次数の垂直分岐は、元の全境界値で仮定なく相殺する。 -/
lemma universalBoundaryValue_vertical_succ (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q + 1⦌)
    (c : Fin (q + 2) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w (q + 1) x
        (.inl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv (r + d) q c).val) =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w (q + 1) x (.inr (.inr c)) := by
  let v := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w
  let z := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv (r + d) q c
  have ho : -((r + d + (q + 1) + 1 - (r + 1) : ℕ) : ℤ) + 1 =
      -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
  rcases hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv z.val.1 v).symm z.val.2 with ⟨a, j⟩
  have ha : a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label z.val.1 v.val z.val.2 := by
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv_symm_color z.val.1 v z.val.2
    rw [hp] at h
    exact h
  subst a
  have hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank z.val.1 v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label z.val.1 v.val z.val.2) z.val.2 := by
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank_symm_colorPositionEquiv z.val.1 v z.val.2
    rw [hp] at h
    exact h.symm
  have hout := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_output_of_pair A S w (q + 1) x z.val.1 z.val.2 ho
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label z.val.1 v.val z.val.2, j⟩ hp
  rw [Sigma.eta] at hout
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_verticalBoundaryFaceEquiv A S v c j hj x
  have ht' := congrArg (fun y =>
    (eqToHom (congrArg (fun n : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X n) ho)).hom y) ht
  rw [map_zsmul] at ht'
  have step {M N P : ModuleCat.{u} A} (hMN : M = N) (hNP : N = P) (y : M) :
      (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
    subst N
    subst P
    rfl
  rw [step] at ht'
  have hdeg : r + d + 1 - (r + 1) = d := by omega
  rw [hdeg] at ht'
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_input, hout]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm, neg_smul, neg_neg]
  convert ht' using 1

/-- C254：既存の全垂直同値によるhvは、全ての正の入力次数で成り立つ。 -/
lemma universalBoundaryValue_vertical_neg (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) (hq : 0 < q)
    (c : Fin (q + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) (q - 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x
        (.inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv (r + d) q hq) c).val) =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x (.inr (.inr c)) := by
  cases q with
  | zero => omega
  | succ q => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_vertical_succ A S w q x c

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
