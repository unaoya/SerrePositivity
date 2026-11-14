module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorLowSimplex
/-!
概要：全切断和から作った二単体データは、元の実 tensor 二単体に厳密に一致する。
方針：三点集合の cochain 比較と全二点集合の辺の比較から、同じ全 Hom 族を照合する。
規約：全次元 HA は未証明。使われ方：全次元候補を二次元で実単体へ昇格する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 全切断和の二単体データは既存の実 tensor 二単体の全データに一致する。 -/
lemma dgNerveTensorDataCandidate_two (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C s t).toSimplexData := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext (s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData)
    (t := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C s t).toSimplexData) rfl
  apply heq_of_eq
  funext I a b k hI ha hb hk
  by_cases hc : I.card = 3
  · have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_eq_univ I hc
    subst I
    have ha' : a = 0 :=
      ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
    have hb' : b = 2 :=
      hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
    have hk' : k = -1 := by simpa using hk
    subst ha' hb' hk'
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorTriangleCandidate_top R B C s t
  · have hle := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hle
    have hc2 : I.card = 2 := by omega
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card (by omega)
      simpa only [← ha, ← hb] using h
    have hpair : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc2
      (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
    have hk' : k = 0 := by omega
    subst hk'
    fin_cases a <;> fin_cases b <;> norm_num at hab
    all_goals subst I
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_pair R B C s.toSimplexData t.toSimplexData 0 1 (by decide)
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_pair R B C s.toSimplexData t.toSimplexData 0 2 (by decide)
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_pair R B C s.toSimplexData t.toSimplexData 1 2 (by decide)
/-- 全切断和の同じデータを保ち、全 HA 方程式を満たす実二単体。 -/
def dgNerveTensorCandidateTwoSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGTensorCategory R B C) 2 where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData
  equation I a b k hI ha hb hk := by
    rw [dgNerveTensorDataCandidate_two R B C s t]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C s t).equation I a b k hI ha hb hk
/-- 候補の全切断和で作った実二単体は元の tensor 二単体と等しい。 -/
lemma dgNerveTensorCandidateTwoSimplex_eq (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    dgNerveTensorCandidateTwoSimplex R B C s t = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C s t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact dgNerveTensorDataCandidate_two R B C s t
end SerrePositivity.InfinityCategories.Project.DerivedCategories
