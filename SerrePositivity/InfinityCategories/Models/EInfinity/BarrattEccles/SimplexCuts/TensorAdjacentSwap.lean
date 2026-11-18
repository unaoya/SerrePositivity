module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorTransport
public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
模型。文献の定義との比較は後で
# 同じ斉次テンソルの一般位置での隣接交換

Berger–Fresse §2.2.4、M14 L11 の証明分割。
元の先頭交換と、元の左テンソルによる尾の交換を同じ斉次元で評価する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open _root_.SerrePositivity.Coxeter

/-- C331：尾の置換は先頭を保って面の族へ作用する（BF §2.2.6）。
方針：有限添字を先頭と後続へ分ける。
規約：出力への作用は添字写像との前合成。
使われ方：隣接交換の尾の再帰式。 -/
lemma cons_comp_shiftPerm {α : Type*} (n : ℕ) (a : α) (f : Fin n → α)
    (σ : Equiv.Perm (Fin n)) :
    Fin.cons a f ∘ shiftPerm σ = Fin.cons a (f ∘ σ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, shiftPerm_zero, Fin.cons_zero]
  · simp only [Function.comp_apply, shiftPerm_succ, Fin.cons_succ]

variable {A : Type u} [CommRing A] (K : Complex A)

/-- C332：同じ斉次テンソルの隣接交換の Koszul 公式（BF §2.2.4）。
方針：先頭二因子の公式と尾の交換の帰納法を使う。
規約：指定した整数全次数を保ち、交換される二面の次数だけが符号を決める。
使われ方：余演算の隣接互換に対する等変性の出力側。 -/
lemma adjacentIso_vectorTensorAt (n : ℕ) (i : Fin n) (f : Fin (n + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (r : ℤ) (hf : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (n + 1) f : ℤ) = r) :
    (adjacentIso K n i).hom.f r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (n + 1) f r hf) =
      ((-((f i.castSucc).1 : ℤ)) *
        (-((f i.succ).1 : ℤ))).negOnePow •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (n + 1) (f ∘ adjacentTransposition i) r
            (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_permutation]; exact hf) := by
  induction n generalizing r with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨a, f, rfl⟩ := Fin.exists_cons f
    revert i
    refine Fin.cases ?_ (fun j => ?_)
    · obtain ⟨b, f, rfl⟩ := Fin.exists_cons f
      have hsum : -(a.1 : ℤ) + (-(b.1 : ℤ) +
          -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n f : ℤ)) = r := by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons] at hf
        omega
      simpa only [adjacentIso, Fin.cases_zero, adjacentTransposition,
        Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_succ,
        Matrix.cons_cons_comp_swap_zero_one] using!
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapFirstIso_vectorTensorAt K n a b f r hsum
    · have hsum : -(a.1 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (n + 1) f : ℤ) = r := by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cons] at hf
        omega
      have hg := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_permutation K (n + 1) f (adjacentTransposition j)
      simp only [← shiftPerm_adjacent, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cons_comp_shiftPerm]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_cons K (n + 1) a f r hsum,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_succ K (n + 1) (Fin.cons a (f ∘ adjacentTransposition j))
          (-(a.1 : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (n + 1) f : ℤ)) r rfl
          (by change -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (n + 1) (f ∘ adjacentTransposition j) : ℤ) = _; rw [hg])
          hsum]
      change (K ◁ (adjacentIso K n j).hom).f r
        (ιTensorObj K (power K (n + 1))
          (-(a.1 : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (n + 1) f : ℤ)) r hsum
          (a.2 ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K (n + 1) f)) = _
      rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply]
      have ht := ih j f (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K (n + 1) f : ℤ)) rfl
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] at ht
      rw [ht]
      simp only [Units.smul_def]
      rw [TensorProduct.tmul_smul, map_zsmul]
      rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
