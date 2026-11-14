module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCutTerm
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorElementHEq
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ空切断の一項から、元の長辺と高次 Hom 成分の tensor を回収する。 -/
lemma dgNerveTensorCutTerm_empty {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (hab : a < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t I a b ∅ k hk hI ha hb (by simp) =
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (s.edgeHom a b hab)
        (t.hom I a b k hI (ha.unique (Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
          (hb.unique (Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))) hk) (zero_add k) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_empty, Int.negOnePow_zero, one_smul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_empty]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C rfl rfl (by simp) (by simpa using hk.symm) rfl
    _ _ _ _ ?_ ?_ _ _
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    apply s.hom_heq_of_indices_degree
    · simp
    · rfl
    · rfl
    · simp
  · exact t.hom_heq_of_indices_degree rfl rfl rfl (by simpa using hk.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
