module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanOnePrefixIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanOnePrefixBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle

/-! # 固定一点の右辺の微分と後続残差の合成

概要：脚側の右辺の微分を、後続の共通残差と脚の合成に符号を掛けた式にする。
方針：余錐頂点の単一寄与を展開し、削除と左切断の既知残差を消す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の cofiber Hom 座標の微分整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：固定一点を加えた右辺の微分は後続残差と脚の合成の符号付きの負。
方針：Bianchi の余錐頂点で右切断を後続集合、左切断を二点の脚と同定する。
規約：符号は (-1)^(n+1)。使われ方：脚側の未知方程式の微分条件。 -/
lemma differential_rhs_span_onePrefix {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (k : ℤ)
    (hI : 2 ≤ (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hmin : a = (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hmax : Fin.last (n + 3) = (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    differential A (s.rhs (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) a (Fin.last (n + 3)) k hI hmin hmax hk) =
      -(((n : ℤ) + 1).negOnePow •
        compose A (s.residual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3))
          (2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ))
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _) rfl)
        (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha)
        (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert a ha] at hk
            rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]
            push_cast at hk ⊢
            omega)) := by
  rw [s.differential_rhs_span_onePrefix_single hknown a ha]
  let I := insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
  have hdel := hknown (I.erase (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_erase_known I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le _).mpr le_rfl))
  have hleft := hknown (I.filter (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_leftCut_known I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n))
  dsimp only [I] at hdel hleft
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution]
  rw [s.residual_zero_of_equation _ hdel, s.residual_zero_of_equation _ hleft]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero, zero_sub]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_rightCut a ha, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_leftCut a ha,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_sign a ha, smul_neg]
  congr 2
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
  congr 1
  all_goals try simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_rightCut a ha, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_leftCut a ha,
    Finset.card_pair (ne_of_lt ha), Nat.cast_ofNat, sub_self]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_rightCut a ha, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_leftCut a ha,
        Finset.card_pair (ne_of_lt ha), Nat.cast_ofNat, sub_self]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (differential_rhs_span_onePrefix)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
