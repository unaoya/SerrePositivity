module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProduct
public import SerrePositivity.DifferentialGraded.Category.Tensor
/-!
概要：同じ内部点の切断合成と選択した第一 Hom 成分から、指定次数の符号付き tensor 項を作る。
方針：同じ実 Hom と切断合成の次数を明示し、有限交差の点数で符号を定める。
規約：SimplexData の候補。HA 方程式と全面・退化への自然性は別途証明が必要。
使われ方：実 dg nerve の直積から tensor nerve への写像の全次元候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ切断項の有限交差符号と極端な切断集合での計算。 -/
def dgNerveTensorCutSign {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (S : Finset (Fin (n + 1))) : ℤ :=
  (((S.product (((I.erase a).erase b).filter (fun j => j ∉ S))).filter
    (fun p => p.1 < p.2)).card : ℤ)
/-- 同じ切断項の有限交差符号と極端な切断集合での計算。 -/
lemma dgNerveTensorCutSign_empty {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) : dgNerveTensorCutSign I a b ∅ = 0 := by
  simp [dgNerveTensorCutSign]
/-- 同じ切断項の有限交差符号と極端な切断集合での計算。 -/
lemma dgNerveTensorCutSign_all {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) : dgNerveTensorCutSign I a b ((I.erase a).erase b) = 0 := by
  simp [dgNerveTensorCutSign]
/-- 元の二つの実 Hom 成分から、指定次数を持つ同じ tensor 成分候補を構成する。 -/
def dgNerveTensorCutTerm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) k := by
  let J := insert a (insert b S)
  have haS : a ∉ S := by intro h; exact (lt_irrefl a) (hc a h).2.1
  have hbS : b ∉ S := by intro h; exact (lt_irrefl b) (hc b h).2.2
  have ha' := ha.unique (Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  have hb' := hb.unique (Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  have hab : a < b := by
    rw [ha', hb']
    exact I.min'_lt_max'_of_card (by omega)
  have hJI : J ⊆ I := by
    apply Finset.insert_subset ha.1
    apply Finset.insert_subset hb.1
    intro j hj
    exact (hc j hj).1
  have haJ : IsLeast (J : Set (Fin (n + 1))) a :=
    ⟨by simp [J], fun _ hj => ha.2 (hJI hj)⟩
  have hbJ : IsGreatest (J : Set (Fin (n + 1))) b :=
    ⟨by simp [J], fun _ hj => hb.2 (hJI hj)⟩
  have hJ : 2 ≤ J.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.two_le_card haJ.1 hbJ.1 (ne_of_lt hab)
  have haBS : a ∉ insert b S := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact (ne_of_lt hab) h
    · exact haS h
  have hcard : J.card = S.card + 2 := by
    dsimp only [J]
    rw [Finset.card_insert_of_notMem haBS, Finset.card_insert_of_notMem hbS]
  let f := s.hom J a b (-(S.card : ℤ)) hJ
    (haJ.unique (Finset.isLeast_min' J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)))
    (hbJ.unique (Finset.isGreatest_max' J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (by omega)
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R C t I a b S hI ha hb hc
  exact (dgNerveTensorCutSign I a b S).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
    (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    f g (by omega)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
