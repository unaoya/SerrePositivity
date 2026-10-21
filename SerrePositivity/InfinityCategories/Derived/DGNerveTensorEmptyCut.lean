module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorCutTerm
public import SerrePositivity.InfinityCategories.Derived.DGTensorElementHEq
public import SerrePositivity.InfinityCategories.DGNerve.Triangle
/-!
概要：空切断の tensor 項は、元の長辺と第二単体の同じ高次成分の tensor に一致する。
方針：実空切断の式と同じ Hom 成分の次数付き比較を、二因子の実 tensor へ渡す。
規約：元の cochain の同定であり、HA 方程式を追加仮定しない。使われ方：全次元候補の低次比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ空切断の一項から、元の長辺と高次 Hom 成分の tensor を回収する。 -/
lemma dgNerveTensorCutTerm_empty {n : ℕ} (s : SimplexData R B n) (t : SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (hab : a < b) :
    dgNerveTensorCutTerm R B C s t I a b ∅ k hk hI ha hb (by simp) =
      dgTensorElement R
        (x := ((s.obj a, t.obj a) : DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : DGTensorCategory R B C))
        (s.edgeHom a b hab)
        (t.hom I a b k hI (ha.unique (Finset.isLeast_min' I (Index.nonempty hI)))
          (hb.unique (Finset.isGreatest_max' I (Index.nonempty hI))) hk) (zero_add k) := by
  unfold dgNerveTensorCutTerm
  dsimp only
  rw [dgNerveTensorCutSign_empty, Int.negOnePow_zero, one_smul, dgNerveCutProduct_empty]
  apply eq_of_heq
  refine dgTensorElement_heq R B C rfl rfl (by simp) (by simpa using hk.symm) rfl
    _ _ _ _ ?_ ?_ _ _
  · dsimp only [SimplexData.edgeHom]
    apply s.hom_heq_of_indices_degree
    · simp
    · rfl
    · rfl
    · simp
  · exact t.hom_heq_of_indices_degree rfl rfl rfl (by simpa using hk.symm)
end SerrePositivity.InfinityCategories
