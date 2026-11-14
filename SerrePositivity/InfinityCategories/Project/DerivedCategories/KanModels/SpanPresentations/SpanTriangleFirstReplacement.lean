module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EraseReplacementComparison

/-! # A 成分の挿入による三角形右辺の変化

概要：A と後続部分の集合の成分を挿入すると、最上位右辺に符号付きの一項を加える。
方針：その集合を二番目の固定頂点の削除集合と同定する。
規約：HA Proposition 1.3.1.10。使われ方：D7 の最後の三角形方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- A 側成分の挿入による三角形右辺の変化は、その成分の変化の符号倍。 -/
lemma spanTwoPrefixRhs_replace_first {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D (n + 3))
    (f : ∀ x y k (hM : 2 ≤ (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card),
      x = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      y = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - ((insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ) → GradedHom R (s.obj x) (s.obj y) k) :
    (s.replace (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) f).spanTwoPrefixRhs - s.spanTwoPrefixRhs =
      ((n : ℤ) + 2).negOnePow •
        (f 0 (Fin.last (n + 3)) (-(n : ℤ) - 2 + 1)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega) -
        s.hom (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (-(n : ℤ) - 2 + 1)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega)) := by
  have H := s.rhs_replace_of_erase_eq Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero (n + 1) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n))
    (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_erase_secondPrefix n)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega) f
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanTwoPrefixRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_sign_secondPrefix] using H

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanTwoPrefixRhs_replace_first)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
