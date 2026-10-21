module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomLiftCoherence
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionFiberCoherence

/-!
概要：元の大域分類 Hom 自然性は、同じ比較 Hom の切断の単位を引き戻したもの。
方針：元の fiber 内比較を同じ単位と照合し、元の零射影で後合成する。
規約：大域自然性・切断・全相対 Hom 作用を保持する。
使われ方：輸送三角形の等式を元の大域分類作用の共有頂点で使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の比較 span の一射影は充満忠実。 -/
lemma cocartesianBaseChangeHomSpanOne_isFullyFaithful :
    IsFullyFaithful (cocartesianBaseChangeHomSpanOne k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact isFullyFaithful_of_trivialKanFibration _

/-- 大域自然性の同じ持ち上げは、元の比較作用の一射影から指定切断で戻る。 -/
lemma cocartesianBaseChangeHomNaturalityLift_section :
    cocartesianBaseChangeHomNaturalityLift k p q =
      (cocartesianBaseChangeHomComparison k p q ≫
        cocartesianBaseChangeHomSpanOne k p q) ≫
          cocartesianBaseChangeHomSpanOneSection k p q := by
  rw [cocartesianBaseChangeHomComparison_one]
  simp only [cocartesianBaseChangeHomNaturalityLift, Category.assoc]

/-- 元の fiber 内自然性同型は、同じ単位を元の比較作用で前合成したもの。 -/
lemma cocartesianBaseChangeHomNaturalityLiftIso_section :
    cocartesianBaseChangeHomNaturalityLiftIso k p q =
      homSpanSectionSourcePrecompIso
        (cocartesianBaseChangeHomSpanOne k p q)
        (cocartesianBaseChangeHomSpanOneSection k p q)
        (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
        (cocartesianBaseChangeHomSpanOneSection_projection k p q)
        (cocartesianBaseChangeHomComparison k p q)
        (cocartesianBaseChangeHomNaturalityLift k p q)
        (cocartesianBaseChangeHomNaturalityLift_section k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact functorIsoOfTrivialKanFibration_eq_sectionUnit
    (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeHomComparison k p q)
    (cocartesianBaseChangeHomNaturalityLift k p q)
    (cocartesianBaseChangeHomNaturalityLift_section k p q)
    (cocartesianBaseChangeHomNaturalityLift_projection k p q)

/-- 元の大域自然性は、同じ切断の単位の零射影を元の全 Hom 作用で引き戻したもの。 -/
lemma cocartesianBaseChangeHomNaturalityIso_section_heq :
    HEq (cocartesianBaseChangeHomNaturalityIso k p q)
      (((homSpanSectionSourceIso
        (cocartesianBaseChangeHomSpanOne k p q)
        (cocartesianBaseChangeHomSpanOneSection k p q)
        (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
        (cocartesianBaseChangeHomSpanOneSection_projection k p q)).postcomp
          (cocartesianBaseChangeHomSpanZero k p q)).precomp
            (cocartesianBaseChangeHomComparison k p q)) := by
  have h := cocartesianBaseChangeHomNaturalityIso_lift_heq k p q
  rw [cocartesianBaseChangeHomNaturalityLiftIso_section] at h
  exact h.trans (homSpanSectionSourcePrecompIso_postcomp_heq
    (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeHomComparison k p q)
    (cocartesianBaseChangeHomNaturalityLift k p q)
    (cocartesianBaseChangeHomNaturalityLift_section k p q)
    (cocartesianBaseChangeHomSpanZero k p q))

end SerrePositivity.InfinityCategories
