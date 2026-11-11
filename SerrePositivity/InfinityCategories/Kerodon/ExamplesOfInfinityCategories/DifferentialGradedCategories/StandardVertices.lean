module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Enrichment
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 標準 Hom の零単体と閉零射の合成

概要：標準零単体の評価は AW 合成と dg 単位を通常の閉零射の合成と単位へ送る。
方針：一点集合での AW の和を評価し、既存の閉零射の合成の計算を使う。
規約：通常の圏は ClosedCategory R D とする。
使われ方：HA 1.3.1.13 の EnrichedOrdinaryCategory の射の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：一点集合での AW 成分は対応する二つの零成分の合成である。
方針：切断点が一つだけなので有限和の唯一の項を取る。
規約：前の射は f、後の射は g。
使われ方：HA 1.3.1.13 の零単体での合成の検査。 -/
lemma awData_singleton {x y z : D} {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f).component {j} 0 (Finset.singleton_nonempty j) (by simp) =
      _root_.SerrePositivity.DifferentialGraded.compose R (g.component {j} 0 (Finset.singleton_nonempty j) (by simp))
        (f.component {j} 0 (Finset.singleton_nonempty j) (by simp)) rfl := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, Finset.sum_eq_single (⟨j, by simp⟩ : ({j} : Finset _))]
  · unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
    simp only [Finset.filter_singleton, le_refl, ite_true]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.compose_eq_of_heq
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq g _ _ rfl _ _ _ _ _ _
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq f _ _ rfl _ _ _ _ _ _
    · change 1 - ((({j} : Finset (Fin (n + 1))).filter (j ≤ ·)).card : ℤ) = 0
      rw [Finset.filter_singleton, ite_eq_left (le_refl j), Finset.card_singleton]
      rfl
    · change 1 - ((({j} : Finset (Fin (n + 1))).filter (· ≤ j)).card : ℤ) = 0
      rw [Finset.filter_singleton, ite_eq_left (le_refl j), Finset.card_singleton]
      rfl
  · intro i _ hi
    exact (hi (Subtype.ext (Finset.mem_singleton.mp i.property))).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- 概要：標準零単体の評価は AW 合成を斉次射の通常順合成へ送る。
方針：Fin 1 の全体集合を一点集合と見て AW の唯一の切断を評価する。
規約：閉元の台の零次数の値として比較する。
使われ方：HA 1.3.1.13 の閉零射との合成の整合性。 -/
lemma standardZeroEval_comp {x y z : D} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z 0)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval (R := R) x z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW g f)).val =
      compose R ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval (R := R) y z) g).val
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval (R := R) x y) f).val rfl := by
  convert awData_singleton g.val f.val (0 : Fin 1) using 1 <;> rfl

/-- 概要：標準単位の零単体の評価は dg 単位である。
方針：定数単体の一点成分の計算を使う。
規約：閉元の部分加群の等号として述べる。
使われ方：HA 1.3.1.13 の通常の圏の恒等射との比較。 -/
lemma standardZeroEval_unit (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval (R := R) x x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) x 0) = unitElement R x := by
  apply Subtype.ext
  convert _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton (unitElement R x) (0 : Fin 1) using 1
  rfl

/-- 概要：閉零射と標準 Hom の零単体は同値である。
方針：閉元への既存の同値と標準零単体の線形同値の逆を合成する。
規約：dg 圏に任意の通常の圏を別途要求しない。
使われ方：HA 1.3.1.13 の単体的圏の通常の射との比較。 -/
@[kerodon 00SF]
def closedStandardVertexEquiv (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :
    (x ⟶ y) ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y) _⦋0⦌ :=
  (closedHomEquiv R D x y).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x y).toEquiv.symm

/-- 概要：閉零射と標準零単体の同値は恒等射を標準単位に送る。
方針：零単体の評価の単射性と dg 単位の評価を使う。
規約：通常の圏の恒等射について述べる。
使われ方：HA 1.3.1.13 の EnrichedOrdinaryCategory の単位の条件。 -/
@[kerodon 00SF]
lemma closedStandardVertexEquiv_id (x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :
    closedStandardVertexEquiv (R := R) (D := D) x x (𝟙 x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) (D := D) x 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x x).injective
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x x)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x x).symm (closedHomEquiv R D x x (𝟙 x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id x).trans (standardZeroEval_unit x).symm

/-- 概要：閉零射と標準零単体の同値は合成を AW 合成へ送る。
方針：零単体の評価で検査し、閉零射と AW 合成の双方の評価の計算を使う。
規約：通常の圏の合成順 f ≫ g と AW の順 g、f を対応させる。
使われ方：HA 1.3.1.13 の EnrichedOrdinaryCategory の合成の条件。 -/
@[kerodon 00SF]
lemma closedStandardVertexEquiv_comp {x y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D} (f : x ⟶ y) (g : y ⟶ z) :
    closedStandardVertexEquiv (R := R) (D := D) x z (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (closedStandardVertexEquiv (R := R) (D := D) y z g)
        (closedStandardVertexEquiv (R := R) (D := D) x y f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x z).injective
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x z)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x z).symm (closedHomEquiv R D x z (f ≫ g))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D x z (f ≫ g)).val =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval (R := R) (D := D) x z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
      (closedStandardVertexEquiv (R := R) (D := D) y z g)
      (closedStandardVertexEquiv (R := R) (D := D) x y f))).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp, standardZeroEval_comp (D := D)]
  have hg := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) y z).apply_symm_apply
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D y z g)
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x y).apply_symm_apply
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D x y f)
  exact congrArg₂ (fun a b ↦ _root_.SerrePositivity.DifferentialGraded.compose R a b rfl)
    (congrArg Subtype.val hg).symm (congrArg Subtype.val hf).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
