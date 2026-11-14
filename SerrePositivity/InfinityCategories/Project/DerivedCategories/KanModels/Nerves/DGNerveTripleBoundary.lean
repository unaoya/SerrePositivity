module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms
/-!
概要：任意次元の実三点成分とその同じ HA 微分式を照合する。
方針：三点集合の唯一の内部点に有限和を集め、元の全 Hom 成分を比較する。
規約：追加の Small 性・平坦性を仮定しない。使われ方：全次元 tensor 候補の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の実単体の生のデータにおける各辺は閉じている。 -/
lemma dgNerveData_edgeHom_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (a b : Fin (n + 1)) (hab : a < b) :
    _root_.SerrePositivity.DifferentialGraded.differential R (s.toSimplexData.edgeHom a b hab) = 0 :=
  s.differential_edgeHom a b hab
/-- 任意の三頂点の HA 右辺は同じ二辺の合成と長辺の差である。 -/
lemma dgNerveTriple_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    s.rhs {a, b, c} a c (-1)
      (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])
      (by symm; exact (Finset.min'_eq_iff _ _ _).2 (by simp [hab.le, (hab.trans hbc).le]))
      (by symm; exact (Finset.max'_eq_iff _ _ _).2 (by simp [hbc.le, (hab.trans hbc).le]))
      (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]) =
    _root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (s.edgeHom b c hbc) (s.edgeHom a b hab) (by decide) -
      s.edgeHom a c (hab.trans hbc) := by
  have hba := ne_of_gt hab
  have hcb := ne_of_gt hbc
  have hca := ne_of_gt (hab.trans hbc)
  have he : ({a, b, c} : Finset (Fin (n + 1))).erase b = {a, c} := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hl : ({a, b, c} : Finset (Fin (n + 1))).filter (· ≤ b) = {a, b} := by
    simp [Finset.filter_insert, Finset.filter_singleton, hab.le, not_le_of_gt hbc]
  have hr : ({a, b, c} : Finset (Fin (n + 1))).filter (b ≤ ·) = {b, c} := by
    simp [Finset.filter_insert, Finset.filter_singleton, hbc.le, not_le_of_gt hab]
  have hs : ({a, b, c} : Finset (Fin (n + 1))).filter (b < ·) = {c} := by
    simp [Finset.filter_insert, Finset.filter_singleton, hbc, not_lt_of_ge hab.le]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  let j0 : ({a, b, c} : Finset (Fin (n + 1))) := ⟨b, by simp⟩
  rw [Finset.sum_eq_single j0]
  · dsimp only [j0]
    rw [dite_eq_left ⟨hab, hbc⟩]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom, he, hl, hr, hs, Finset.card_singleton,
      Int.natCast_one, Int.negOnePow_one, Units.neg_smul, one_smul]
    norm_num
    refine congrArg₂ (fun (f g : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj c) 0) => f - g) ?_ ?_
    · apply eq_of_heq
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl
        (by simp [hl, ne_of_lt hab]) (by simp [hr, ne_of_lt hbc]) (by decide)
        _ _ _ _ ?_ ?_ _ _
      · exact s.hom_heq_of_indices_degree rfl rfl rfl (by simp [hr, ne_of_lt hbc])
      · exact s.hom_heq_of_indices_degree rfl rfl rfl (by simp [hl, ne_of_lt hab])
    · exact eq_of_heq (s.hom_heq_of_indices_degree rfl rfl rfl (by decide))
  · intro j _ hj
    rcases j with ⟨j, hjI⟩
    rcases Finset.mem_insert.mp hjI with rfl | hjI
    · simp
    · rcases Finset.mem_insert.mp hjI with rfl | hjI
      · exact (hj (Subtype.ext rfl)).elim
      · have : j = c := Finset.mem_singleton.mp hjI
        subst j
        simp
  · intro h
    exact (h (Finset.mem_univ j0)).elim
/-- 実単体の任意の三点 cochain の微分は、同じ二辺の合成と長辺の差。 -/
lemma dgNerveTripleHom_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    _root_.SerrePositivity.DifferentialGraded.differential R (s.toSimplexData.tripleHom a b c hab hbc) =
      _root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (s.edgeHom b c hbc) (s.edgeHom a b hab) (by decide) -
        s.edgeHom a c (hab.trans hbc) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom, s.equation, dgNerveTriple_rhs R D s.toSimplexData a b c hab hbc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
