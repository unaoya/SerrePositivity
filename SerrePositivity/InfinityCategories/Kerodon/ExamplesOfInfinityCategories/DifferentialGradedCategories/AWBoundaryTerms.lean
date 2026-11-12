module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWTensorDifferential

/-!
# AW の境界の非対角項と対角項の同定

概要：非対角境界項を削除後の AW の制限項に同定し、隣接する対角項を相殺する。
方針：連続区間の面の交換公式を、全テンソルへの斉次制限項に適用する。
規約：KST Construction A.5 の標準 AW。全次数は p+q=n、元の単体の次元は n+1。
使われ方：境界添字の同値と合わせた AW の鎖写像性。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：前半の非対角の面は、全単体の対応する頂点を削除した後の切断項。
方針：前半の局所面の公式と、後半の始点より前の削除の公式を使う。
規約：KST A.5、k≤p。使われ方：水平境界の非対角項の同定。 -/
lemma awLeftBoundaryTerm {p q n : ℕ} (h : p + q = n) (k : Fin (p + 1)) :
    awTensorTerm C D
      (SimplexCategory.δ k.castSucc ≫ awInterval 0 (p + 1) (n + 1) (by omega))
      (awInterval (p + 1) q (n + 1) (by omega)) h =
    awTensorTerm C D
      (awInterval 0 p n (by omega) ≫
        SimplexCategory.δ (⟨k, by have := k.isLt; omega⟩ : Fin (n + 2)))
      (awInterval p q n (by omega) ≫
        SimplexCategory.δ (⟨k, by have := k.isLt; omega⟩ : Fin (n + 2))) h := by
  have hf : SimplexCategory.δ k.castSucc ≫ awInterval 0 (p + 1) (n + 1) (by omega) =
      awInterval 0 p n (by omega) ≫
        SimplexCategory.δ (⟨k, by have := k.isLt; omega⟩ : Fin (n + 2)) := by
    simpa only [Nat.zero_add, Fin.val_castSucc] using
      awInterval_face_inside 0 p n (by omega) k.castSucc
  have hg := awInterval_face_before p q n (by omega)
    (⟨k, by have := k.isLt; omega⟩ : Fin (n + 2))
    (by change (k : ℕ) ≤ p; exact Nat.le_of_lt_succ k.isLt)
  rw [hf, hg]

/-- 概要：後半の非対角の面は、全単体の対応する頂点を削除した後の切断項。
方針：後半の局所面の公式と、前半の終点より後の削除の公式を使う。
規約：KST A.5、局所面は k+1。使われ方：垂直境界の非対角項の同定。 -/
lemma awRightBoundaryTerm {p q n : ℕ} (h : p + q = n) (k : Fin (q + 1)) :
    awTensorTerm C D
      (awInterval 0 p (n + 1) (by omega))
      (SimplexCategory.δ k.succ ≫ awInterval p (q + 1) (n + 1) (by omega)) h =
    awTensorTerm C D
      (awInterval 0 p n (by omega) ≫
        SimplexCategory.δ (⟨p + ((k : ℕ) + 1), by have := k.isLt; omega⟩ : Fin (n + 2)))
      (awInterval p q n (by omega) ≫
        SimplexCategory.δ (⟨p + ((k : ℕ) + 1), by have := k.isLt; omega⟩ : Fin (n + 2))) h := by
  have hg : SimplexCategory.δ k.succ ≫ awInterval p (q + 1) (n + 1) (by omega) =
      awInterval p q n (by omega) ≫
        SimplexCategory.δ (⟨p + ((k : ℕ) + 1), by have := k.isLt; omega⟩ : Fin (n + 2)) :=
    awInterval_face_inside p q n (by omega) k.succ
  have hf := awInterval_face_after 0 p n (by omega)
    (⟨p + ((k : ℕ) + 1), by have := k.isLt; omega⟩ : Fin (n + 2))
    (by change 0 + p < p + ((k : ℕ) + 1); omega)
  rw [hg, hf]

/-- 概要：隣接する切断点の水平・垂直の対角境界項は等しい制限項を持つ。
方針：前半の最後の頂点の削除と、後半の最初の頂点の削除を評価する。
規約：KST A.5、符号を付ける前の等式。
使われ方：標準の全複体の符号による相殺。 -/
lemma awDiagonalBoundaryTerm {p q n : ℕ} (h : p + q = n) :
    awTensorTerm C D
      (SimplexCategory.δ (Fin.last (p + 1)) ≫ awInterval 0 (p + 1) (n + 1) (by omega))
      (awInterval (p + 1) q (n + 1) (by omega)) h =
    awTensorTerm C D (awInterval 0 p (n + 1) (by omega))
      (SimplexCategory.δ (0 : Fin (q + 2)) ≫ awInterval p (q + 1) (n + 1) (by omega)) h := by
  rw [awInterval_face_last, awInterval_face_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
