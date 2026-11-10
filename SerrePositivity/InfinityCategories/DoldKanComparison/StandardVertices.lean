module

public import SerrePositivity.InfinityCategories.DoldKanComparison.Enrichment
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 標準 Hom の零単体と閉零射の合成

概要：標準零単体の評価は AW 合成と dg 単位を通常の閉零射の合成と単位へ送る。
方針：一点集合での AW の和を評価し、既存の閉零射の合成の計算を使う。
規約：通常の圏は ClosedCategory R D とする。
使われ方：HA 1.3.1.13 の EnrichedOrdinaryCategory の射の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded DGNerve.PinchedHom MonoidalCategory
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：一点集合での AW 成分は対応する二つの零成分の合成である。
方針：切断点が一つだけなので有限和の唯一の項を取る。
規約：前の射は f、後の射は g。
使われ方：HA 1.3.1.13 の零単体での合成の検査。 -/
lemma awData_singleton {x y z : D} {n : ℕ} (g : LinearData R y z n)
    (f : LinearData R x y n) (j : Fin (n + 1)) :
    (awData g f).component {j} 0 (Finset.singleton_nonempty j) (by simp) =
      compose R (g.component {j} 0 (Finset.singleton_nonempty j) (by simp))
        (f.component {j} 0 (Finset.singleton_nonempty j) (by simp)) rfl := by
  rw [awData_component, Finset.sum_eq_single (⟨j, by simp⟩ : ({j} : Finset _))]
  · unfold awTerm
    simp only [Finset.filter_singleton, le_refl, ite_true]
    apply compose_eq_of_heq
    · exact component_heq_of_eq g _ _ rfl _ _ _ _ _ _
    · exact component_heq_of_eq f _ _ rfl _ _ _ _ _ _
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
lemma standardZeroEval_comp {x y z : D} (g : StandardSimplex R y z 0)
    (f : StandardSimplex R x y 0) :
    ((standardZeroEval (R := R) x z) (standardAW g f)).val =
      compose R ((standardZeroEval (R := R) y z) g).val
        ((standardZeroEval (R := R) x y) f).val rfl := by
  convert awData_singleton g.val f.val (0 : Fin 1) using 1 <;> rfl

/-- 概要：標準単位の零単体の評価は dg 単位である。
方針：定数単体の一点成分の計算を使う。
規約：閉元の部分加群の等号として述べる。
使われ方：HA 1.3.1.13 の通常の圏の恒等射との比較。 -/
lemma standardZeroEval_unit (x : D) :
    standardZeroEval (R := R) x x (standardUnit (R := R) x 0) = unitElement R x := by
  apply Subtype.ext
  convert standardConstant_singleton (unitElement R x) (0 : Fin 1) using 1
  rfl

/-- 概要：閉零射と標準 Hom の零単体は同値である。
方針：閉元への既存の同値と標準零単体の線形同値の逆を合成する。
規約：dg 圏に任意の通常の圏を別途要求しない。
使われ方：HA 1.3.1.13 の単体的圏の通常の射との比較。 -/
@[kerodon 00SF]
def closedStandardVertexEquiv (x y : ClosedCategory R D) :
    (x ⟶ y) ≃ (standardHomSpace (R := R) (D := D) x y) _⦋0⦌ :=
  (closedHomEquiv R D x y).trans (standardZeroEquiv (R := R) (D := D) x y).toEquiv.symm

/-- 概要：閉零射と標準零単体の同値は恒等射を標準単位に送る。
方針：零単体の評価の単射性と dg 単位の評価を使う。
規約：通常の圏の恒等射について述べる。
使われ方：HA 1.3.1.13 の EnrichedOrdinaryCategory の単位の条件。 -/
@[kerodon 00SF]
lemma closedStandardVertexEquiv_id (x : ClosedCategory R D) :
    closedStandardVertexEquiv (R := R) (D := D) x x (𝟙 x) =
      standardUnit (R := R) (D := D) x 0 := by
  apply (standardZeroEquiv (R := R) (D := D) x x).injective
  change (standardZeroEquiv (R := R) (D := D) x x)
    ((standardZeroEquiv (R := R) (D := D) x x).symm (closedHomEquiv R D x x (𝟙 x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (DGNerve.HomotopyComparison.closedHom_id x).trans (standardZeroEval_unit x).symm

/-- 概要：閉零射と標準零単体の同値は合成を AW 合成へ送る。
方針：零単体の評価で検査し、閉零射と AW 合成の双方の評価の計算を使う。
規約：通常の圏の合成順 f ≫ g と AW の順 g、f を対応させる。
使われ方：HA 1.3.1.13 の EnrichedOrdinaryCategory の合成の条件。 -/
@[kerodon 00SF]
lemma closedStandardVertexEquiv_comp {x y z : ClosedCategory R D} (f : x ⟶ y) (g : y ⟶ z) :
    closedStandardVertexEquiv (R := R) (D := D) x z (f ≫ g) =
      standardAW (closedStandardVertexEquiv (R := R) (D := D) y z g)
        (closedStandardVertexEquiv (R := R) (D := D) x y f) := by
  apply (standardZeroEquiv (R := R) (D := D) x z).injective
  change (standardZeroEquiv (R := R) (D := D) x z)
    ((standardZeroEquiv (R := R) (D := D) x z).symm (closedHomEquiv R D x z (f ≫ g))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (closedHomEquiv R D x z (f ≫ g)).val =
    ((standardZeroEval (R := R) (D := D) x z) (standardAW
      (closedStandardVertexEquiv (R := R) (D := D) y z g)
      (closedStandardVertexEquiv (R := R) (D := D) x y f))).val
  rw [DGNerve.HomotopyComparison.closedHom_comp, standardZeroEval_comp (D := D)]
  have hg := (standardZeroEquiv (R := R) (D := D) y z).apply_symm_apply
    (closedHomEquiv R D y z g)
  have hf := (standardZeroEquiv (R := R) (D := D) x y).apply_symm_apply
    (closedHomEquiv R D x y f)
  exact congrArg₂ (fun a b ↦ compose R a b rfl)
    (congrArg Subtype.val hg).symm (congrArg Subtype.val hf).symm

end SerrePositivity.InfinityCategories.DoldKanComparison
