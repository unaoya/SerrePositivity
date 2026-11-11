module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecompositionFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom

/-! # dg nerve の低次単体の外延性

概要：二単体を対象・三辺・三点ホモトピーの一致で比較する。
方針：部分集合を濃度二・三に分け、四つの指定成分へ帰着する。
規約：対象の等式に沿う異種等号を使う。使われ方：D7 の比較三単体の面の照合。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 二単体は対象・三辺・三点成分で定まる。 -/
lemma dgSimplex2_ext (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2) (hobj : s.obj = t.obj)
    (h01 : HEq (s.toSimplexData.edgeHom 0 1 (by decide))
      (t.toSimplexData.edgeHom 0 1 (by decide)))
    (h12 : HEq (s.toSimplexData.edgeHom 1 2 (by decide))
      (t.toSimplexData.edgeHom 1 2 (by decide)))
    (h02 : HEq (s.toSimplexData.edgeHom 0 2 (by decide))
      (t.toSimplexData.edgeHom 0 2 (by decide)))
    (h012 : HEq (s.toSimplexData.tripleHom 0 1 2 (by decide) (by decide))
      (t.toSimplexData.tripleHom 0 1 2 (by decide) (by decide))) : s = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  by_cases hc : I.card = 3
  · have hU : I = Finset.univ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_eq_univ I hc
    subst I
    have ha' : a = 0 := ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
    have hb' : b = 2 := hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
    have hk' : k = -1 := by simpa using hk
    subst ha' hb' hk'
    have hU : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom, hU] using h012
  · have hle := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hle
    have hc2 : I.card = 2 := by omega
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card hI
    have hpair : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc2
      (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
    have hk' : k = 0 := by omega
    subst k
    fin_cases a <;> fin_cases b <;> norm_num at hab
    all_goals subst I
    · exact h01
    · exact h02
    · exact h12


/-- 一単体は二頂点と辺の成分で定まる。 -/
lemma dgSimplex1_ext (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 1) (hobj : s.obj = t.obj)
    (h01 : HEq (s.toSimplexData.edgeHom 0 1 (by decide))
      (t.toSimplexData.edgeHom 0 1 (by decide))) : s = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  have hU := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.two_eq_univ I hI
  subst I
  have ha' : a = 0 := ha.trans ((Finset.min'_eq_iff _ _ 0).2
    ⟨by simp, fun x _ => Fin.zero_le x⟩)
  have hb' : b = 1 := hb.trans ((Finset.max'_eq_iff _ _ 1).2
    ⟨by simp, fun x _ => Fin.le_last x⟩)
  have hk' : k = 0 := by simpa using hk
  subst ha' hb' hk'
  have hU : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom, hU] using h01

end SerrePositivity.InfinityCategories.Project.DerivedCategories
