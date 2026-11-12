module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData

/-! # 次次数の標準退化錐の表示独立性

概要：同じ図式単体の異なる基本退化表示から作る標準錐は全次数で厳密に一致する。
方針：異なる退化番号の重なりを二重退化へ戻し、下次数錐の退化式と σσ 恒等式を使う。
規約：零次元も含む。使われ方：次次数の充填の退化正規化。
-/
@[expose] public section

open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
universe u
variable {K X : SSet.{u}} {f : K ⟶ X}

/-- 異なる基本退化像の重なりでは標準錐が一致する。 -/
lemma truncatedConeDegeneracy_overlap {n : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f (n + 1))
    (i j : Fin (n + 1)) (hij : i ≤ j) (y z : K _⦋n + 1⦌)
    (h : K.σ i.castSucc y = K.σ j.succ z) :
    X.σ i.castSucc.succ (C.simplex (n + 1) le_rfl y) =
      X.σ j.succ.succ (C.simplex (n + 1) le_rfl z) := by
  have hy : y = K.σ j (K.δ i.castSucc z) :=
    (K.δ_comp_σ_self_apply i.castSucc y).symm.trans
      ((congrArg (K.δ i.castSucc.castSucc) h).trans
        (K.δ_comp_σ_of_le_apply (Fin.castSucc_le_castSucc_iff.mpr hij) z))
  have hz : z = K.σ i (K.δ j.succ y) :=
    (K.δ_comp_σ_succ_apply j.succ z).symm.trans
      ((congrArg (K.δ j.succ.succ) h.symm).trans
        (K.δ_comp_σ_of_gt_apply (by simpa using hij) y))
  have hw : K.δ j.succ y = K.δ i.castSucc z :=
    (congrArg (K.δ j.succ) hy).trans
      (K.δ_comp_σ_succ_apply j (K.δ i.castSucc z))
  have hz' := hz.trans (congrArg (K.σ i) hw)
  have hl := (congrArg (C.simplex (n + 1) le_rfl) hy).trans
    (C.degeneracy_positive n le_rfl (K.δ i.castSucc z) j).symm
  have hr := (congrArg (C.simplex (n + 1) le_rfl) hz').trans
    (C.degeneracy_positive n le_rfl (K.δ i.castSucc z) i).symm
  rw [hl, hr]
  simpa only [Fin.castSucc_succ] using
    X.σ_comp_σ_apply (Fin.succ_le_succ_iff.mpr hij)
      (C.simplex n (by omega) (K.δ i.castSucc z))
/-- 任意の基本退化表示の選択は同じ標準錐を与える。 -/
lemma truncatedConeDegeneracy_congr {N : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (i j : Fin (N + 1)) (y z : K _⦋N⦌) (h : K.σ i y = K.σ j z) :
    X.σ i.succ (C.simplex N le_rfl y) = X.σ j.succ (C.simplex N le_rfl z) := by
  have same (i : Fin (N + 1)) (y z : K _⦋N⦌) (h : K.σ i y = K.σ i z) :
      y = z := (K.δ_comp_σ_self_apply i y).symm.trans
        ((congrArg (K.δ i.castSucc) h).trans (K.δ_comp_σ_self_apply i z))
  have ordered (i j : Fin (N + 1)) (hij : i < j)
      (y z : K _⦋N⦌) (h : K.σ i y = K.σ j z) :
      X.σ i.succ (C.simplex N le_rfl y) =
        X.σ j.succ (C.simplex N le_rfl z) := by
    cases N with
    | zero =>
      have hi := i.isLt
      have hj := j.isLt
      have hh : i.val < j.val := hij
      omega
    | succ n =>
      have hi : i ≠ Fin.last (n + 1) := by
        intro he
        have hh : i.val < j.val := hij
        rw [he, Fin.val_last] at hh
        omega
      have hj : j ≠ 0 := by
        intro he
        subst j
        exact Fin.not_lt_zero i hij
      have hle : i.castPred hi ≤ j.pred hj := by
        change i.val ≤ j.val - 1
        omega
      have he := truncatedConeDegeneracy_overlap C (i.castPred hi) (j.pred hj) hle y z
      have ht : K.σ (i.castPred hi).castSucc y = K.σ (j.pred hj).succ z := by
        simpa only [Fin.castSucc_castPred, Fin.succ_pred] using h
      simpa only [Fin.castSucc_castPred, Fin.succ_pred] using he ht
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j hij y z h
  · exact congrArg (fun w => X.σ i.succ (C.simplex N le_rfl w)) (same i y z h)
  · exact (ordered j i hji z y h.symm).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
