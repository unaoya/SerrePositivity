module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutLeibniz
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCutTerm
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCandidate
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorElementCalculus
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual
/-!
概要：全次元 tensor 候補の同じ切断項と有限和の微分を、元のブロックの HA 右辺へ展開する。
方針：選択した第一成分とその HA 右辺を取り出し、tensor と切断合成の Leibniz 則を適用する。
規約：展開した block 右辺と候補自身の HA 右辺の一致は別途必要。使われ方：高次 HA の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 両端と選択した切断点だけを持つ、元の第一 Hom 成分。 -/
def dgNerveSelectedCutHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (a b : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hab : a < b)
    (hc : ∀ j ∈ S, a < j ∧ j < b) : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (-(S.card : ℤ)) := by
  let J := insert a (insert b S)
  have haS : a ∉ S := by intro h; exact (lt_irrefl a) (hc a h).1
  have hbS : b ∉ S := by intro h; exact (lt_irrefl b) (hc b h).2
  have haBS : a ∉ insert b S := by simp [ne_of_lt hab, haS]
  have hcard : J.card = S.card + 2 := by
    dsimp only [J]
    rw [Finset.card_insert_of_notMem haBS, Finset.card_insert_of_notMem hbS]
  have hJ : 2 ≤ J.card := by omega
  have haJ : IsLeast (J : Set (Fin (n + 1))) a := by
    refine ⟨by simp [J], ?_⟩
    intro j hj
    change j ∈ J at hj
    simp only [J, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact le_rfl
    · exact hab.le
    · exact (hc j hj).1.le
  have hbJ : IsGreatest (J : Set (Fin (n + 1))) b := by
    refine ⟨by simp [J], ?_⟩
    intro j hj
    change j ∈ J at hj
    simp only [J, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact hab.le
    · exact le_rfl
    · exact (hc j hj).2.le
  exact s.hom J a b (-(S.card : ℤ)) hJ
    (haJ.unique (Finset.isLeast_min' J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)))
    (hbJ.unique (Finset.isGreatest_max' J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (by omega)
/-- 両端と選択した切断点だけを持つ、元の第一成分の HA 右辺。 -/
def dgNerveSelectedCutRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (a b : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hab : a < b)
    (hc : ∀ j ∈ S, a < j ∧ j < b) : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (-(S.card : ℤ) + 1) := by
  let J := insert a (insert b S)
  have haS : a ∉ S := by intro h; exact (lt_irrefl a) (hc a h).1
  have hbS : b ∉ S := by intro h; exact (lt_irrefl b) (hc b h).2
  have haBS : a ∉ insert b S := by simp [ne_of_lt hab, haS]
  have hcard : J.card = S.card + 2 := by
    dsimp only [J]
    rw [Finset.card_insert_of_notMem haBS, Finset.card_insert_of_notMem hbS]
  have hJ : 2 ≤ J.card := by omega
  have haJ : IsLeast (J : Set (Fin (n + 1))) a := by
    refine ⟨by simp [J], ?_⟩
    intro j hj
    change j ∈ J at hj
    simp only [J, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact le_rfl
    · exact hab.le
    · exact (hc j hj).1.le
  have hbJ : IsGreatest (J : Set (Fin (n + 1))) b := by
    refine ⟨by simp [J], ?_⟩
    intro j hj
    change j ∈ J at hj
    simp only [J, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact hab.le
    · exact le_rfl
    · exact (hc j hj).2.le
  exact s.rhs J a b (-(S.card : ℤ)) hJ
    (haJ.unique (Finset.isLeast_min' J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)))
    (hbJ.unique (Finset.isGreatest_max' J (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (by omega)
/-- 実単体の同じ第一選択成分の微分は、その HA 右辺に一致する。 -/
lemma dgNerveSelectedCutHom_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (a b : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hab : a < b)
    (hc : ∀ j ∈ S, a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.differential R (dgNerveSelectedCutHom R D s.toSimplexData a b S hab hc) =
      dgNerveSelectedCutRhs R D s.toSimplexData a b S hab hc := by
  unfold dgNerveSelectedCutHom dgNerveSelectedCutRhs
  dsimp only
  rw [s.equation]
variable (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ符号付き切断項を、第一選択成分と第二切断合成で厳密に表示する。 -/
lemma dgNerveTensorCutTerm_eq_selected {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hab : a < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t I a b S k hk hI ha hb hc =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S).negOnePow • dgTensorElement R
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (dgNerveSelectedCutHom R B s a b S hab (fun j hj => (hc j hj).2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R C t I a b S hI ha hb hc) (by omega) := by
  rfl
/-- 同じ tensor 切断項の微分を、元の両ブロックの HA 右辺へ明示的に展開する。 -/
lemma dgNerveTensorCutTerm_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hab : a < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData
      I a b S k hk hI ha hb hc) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S).negOnePow •
      (_root_.SerrePositivity.DifferentialGraded.dgTensorElement R
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (dgNerveSelectedCutRhs R B s.toSimplexData a b S hab (fun j hj => (hc j hj).2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R C t.toSimplexData I a b S hI ha hb hc) (by omega) +
      (-(S.card : ℤ)).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (dgNerveSelectedCutHom R B s.toSimplexData a b S hab (fun j hj => (hc j hj).2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R C t.toSimplexData I a b S hI ha hb hc) (by omega)) := by
  rw [dgNerveTensorCutTerm_eq_selected R B C s.toSimplexData t.toSimplexData
    I a b S k hk hI ha hb hc hab]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_differential R B C,
    dgNerveSelectedCutHom_differential R B s a b S hab (fun j hj => (hc j hj).2),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_differential_eq_rhs R C t I a b S hI ha hb hc]
/-- 元の両入力の HA 右辺を代入した、同じ切断項の展開。 -/
def dgNerveTensorCutBlockRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)),
      ← hb.unique (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))] using h
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S).negOnePow •
    (_root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (dgNerveSelectedCutRhs R B s a b S hab (fun j hj => (hc j hj).2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R C t I a b S hI ha hb hc) (by omega) +
    (-(S.card : ℤ)).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (dgNerveSelectedCutHom R B s a b S hab (fun j hj => (hc j hj).2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R C t I a b S hI ha hb hc) (by omega))
/-- 実二入力の同じ切断項の微分は、元の HA ブロック展開に一致する。 -/
lemma dgNerveTensorCutTerm_differential_eq_blockRhs {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData
      I a b S k hk hI ha hb hc) =
      dgNerveTensorCutBlockRhs R B C s.toSimplexData t.toSimplexData I a b S k hk hI ha hb hc := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)),
      ← hb.unique (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))] using h
  unfold dgNerveTensorCutBlockRhs
  exact dgNerveTensorCutTerm_differential R B C s t I a b S k hk hI ha hb hc hab
open scoped BigOperators
/-- 全切断集合にわたる、元の HA ブロック展開の同じ符号付き有限和。 -/
def dgNerveTensorBlockRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) :=
  ∑ S : (I.filter (fun j => a < j ∧ j < b)).powerset,
    dgNerveTensorCutBlockRhs R B C s t I a b S.val k hk hI ha hb (by
      intro j hj
      exact Finset.mem_filter.mp (Finset.mem_powerset.mp S.property hj))
/-- 実二入力の全次元候補の微分は、元の HA ブロック展開の有限和に一致する。 -/
lemma dgNerveTensorHomCandidate_differential_eq_blockRhs {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
      I a b k hk hI ha hb) =
      dgNerveTensorBlockRhs R B C s.toSimplexData t.toSimplexData I a b k hk hI ha hb := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate dgNerveTensorBlockRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sum (A := R) (D := DGTensorCategory R B C)]
  apply Finset.sum_congr rfl
  intro S _
  exact dgNerveTensorCutTerm_differential_eq_blockRhs R B C s t I a b S.val k hk hI ha hb (by
    intro j hj
    exact Finset.mem_filter.mp (Finset.mem_powerset.mp S.property hj))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
