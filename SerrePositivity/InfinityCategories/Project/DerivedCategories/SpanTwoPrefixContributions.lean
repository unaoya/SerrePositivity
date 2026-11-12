module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanTwoPrefixBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom

/-! # 二固定頂点の Bianchi の個々の寄与

概要：二つの残差寄与を、後続残差と三角形成分の合成、および脚側残差の差へ展開する。
方針：削除集合と左右切断を同定し、既知残差を消して符号を評価する。
規約：HA Proposition 1.3.1.10。使われ方：D7 の六成分の残差整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：余錐頂点の寄与は後続残差と三角形成分の合成の符号付きの負。
方針：削除と左切断の既知残差を消し、右切断を後続集合に置き換える。
規約：係数は (-1)^(n+1)。使われ方：三角形のホモトピーによる残差項。 -/
lemma span_twoPrefix_contribution_apex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : Fin.last (n + 3) = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    s.residualContribution Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n) =
      ((n : ℤ) + 1).negOnePow •
        (-compose A (s.residual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3))
          (2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ))
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _) rfl)
        (s.tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
        (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) := by
  let V : Finset (Fin (n + 4)) := Finset.univ
  have hdel := hknown (V.erase (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_erase_known V (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le _).mpr le_rfl))
  have hleft := hknown (V.filter (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_leftCut_known V (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n))
  dsimp only [V] at hdel hleft
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution]
  rw [s.residual_zero_of_equation _ hdel, s.residual_zero_of_equation _ hleft]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero, zero_sub, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_sign_apex,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_rightCut_apex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_leftCut_apex]
  have hcard : ({0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n} : Finset (Fin (n + 4))).card = 3 := by
    simp [ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n), ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n),
      ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]
  congr 2
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom]
  congr 1
  all_goals try simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_rightCut_apex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_leftCut_apex, hcard, Nat.cast_ofNat]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_rightCut_apex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_leftCut_apex, hcard, Nat.cast_ofNat]
  all_goals omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (span_twoPrefix_contribution_apex)


/-- 概要：二番目の固定点の寄与は A 側残差と脚側残差の合成との差に符号を掛けた式。
方針：左切断の既知残差を消し、削除と右切断を一点追加集合へ置き換える。
規約：係数は (-1)^(n+2)。使われ方：二脚から得る残差の比較。 -/
lemma span_twoPrefix_contribution_secondPrefix {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : Fin.last (n + 3) = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    s.residualContribution Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n)) =
      ((n : ℤ) + 2).negOnePow •
        (s.residual (insert (0 : Fin (n + 4)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3))
          (k + 1)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]
              simp only [Finset.card_univ, Fintype.card_fin] at hk
              push_cast at hk ⊢
              omega) -
        compose A (s.residual (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Fin.last (n + 3))
          (2 - ((insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ))
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; omega)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _) rfl)
          (s.edgeHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n))
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]
              simp only [Finset.card_univ, Fintype.card_fin] at hk
              push_cast at hk ⊢
              omega)) := by
  let V : Finset (Fin (n + 4)) := Finset.univ
  have hleft := hknown (V.filter (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_leftCut_known V (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n)))
  dsimp only [V] at hleft
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution]
  rw [s.residual_zero_of_equation _ hleft]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_sign_secondPrefix,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_leftCut_secondPrefix, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_rightCut_secondPrefix, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_erase_secondPrefix]
  congr 1
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
  congr 1
  all_goals congr 1
  all_goals try simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_leftCut_secondPrefix, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_rightCut_secondPrefix,
    Finset.card_pair (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)),
    Nat.cast_ofNat, sub_self]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_leftCut_secondPrefix, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUniv_rightCut_secondPrefix,
        Finset.card_pair (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)),
        Nat.cast_ofNat, sub_self]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (span_twoPrefix_contribution_secondPrefix)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
