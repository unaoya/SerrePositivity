module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorFamilyBlocks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorCoInsertionEvaluation

/-!
模型。文献の定義との比較は後で
# 元の指定因子への余代入の斉次テンソル評価

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則。
報告 §295 の元の有限族・指定整数次数・余代入を保った評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts (prefixFamily suffixFamily insertionFamily family_eq_blocks
  insertionFamily_eq_blocks tensorCoInsertionAction_on_blocks)
variable {A : Type u} [CommRing A]

/-- 概要：元の出力族上の余代入は前方次数の Koszul 符号付きの置換族（BF §3.1）。
方針：元の面テンソルを三ブロックへ分け、実際の余代入のブロック評価と再連結を使う。
規約：内側作用の一つの指定面テンソル値と整数係数を保持する。
使われ方：実際の内側辺・頂点の余演算の各項を共通出力族へ送る。 -/
lemma tensorCoInsertionAction_vector_apply (K C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ K ⟶ power K n)
    (c z : ℤ) (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (m - i.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i) : ℤ))) = z)
    (a : C.X c) (hg : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ) = c + -((f i).1 : ℤ))
    (r : ℤ) (hθ : θ.f (c + -((f i).1 : ℤ))
      (ιTensorObj C K c (-((f i).1 : ℤ))
        (c + -((f i).1 : ℤ)) rfl (a ⊗ₜ[A] (f i).2)) =
      r • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n g (c + -((f i).1 : ℤ)) hg) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction K C m n i θ).f z
      (ιTensorObj C (power K (m + 1)) c
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (m - i.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i) : ℤ)))
        z hz (a ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + 1) f _ (by
          have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_family_blocks K f i; omega))) =
      (c * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) : ℤ)).negOnePow •
        (r • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily f g i) z (by
          rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_insertionFamily]; omega)) := by
  let p := -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) : ℤ)
  let q := -((f i).1 : ℤ)
  let b := -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (m - i.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i) : ℤ)
  have hf : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (m + 1) f : ℤ) = p + (q + b) := by
    have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_family_blocks K f i
    dsimp only [p, q, b]
    omega
  let x := ιTensorObj C (power K i.val ⊗
      (K ⊗ power K (m - i.val))) c (p + (q + b)) z hz
    (a ⊗ₜ[A] ιTensorObj (power K i.val)
      (K ⊗ power K (m - i.val)) p (q + b) (p + (q + b)) rfl
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) ⊗ₜ[A]
        ιTensorObj K (power K (m - i.val)) q b (q + b) rfl
          ((f i).2 ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K (m - i.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i))))
  have H := congrArg (fun φ => φ.f z x)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorCoInsertionAction_on_blocks K C m n i θ)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
  have hinput : (C ◁ ((appendIso K i.val (m - i.val + 1)).hom ≫
      eqToHom (congrArg (power K)
        (by omega : i.val + (m - i.val + 1) = m + 1)))).f z x =
      ιTensorObj C (power K (m + 1)) c (p + (q + b)) z hz
        (a ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (m + 1) f (p + (q + b)) hf) := by
    dsimp only [x]
    erw [SerrePositivity.DifferentialGraded.whiskerLeft_apply]
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    erw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_family_blocks K f i (p + (q + b)) hf]
  rw [hinput] at H
  rw [H]
  dsimp only [x, p, q, b]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coInsertionBlocks_vector_apply K C i.val n (m - i.val) θ c _ z
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i) hz a ((f i).2) hg r hθ]
  simp only [Units.smul_def, map_zsmul]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_arity_transport K
    (by omega : i.val + (n + (m - i.val)) = m + n)
    (Fin.append (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) (Fin.append g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i))) z
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; omega)]
  simp only [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily_eq_blocks f g i]


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
