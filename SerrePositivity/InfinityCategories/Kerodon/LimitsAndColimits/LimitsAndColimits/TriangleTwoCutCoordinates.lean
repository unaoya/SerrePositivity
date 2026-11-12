module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLabelPathCoordinates

/-!
概要：三対象の path の、零側と中間側の二つの切断座標。
方針：二つの閾値で既存の最大零座標を使い、中間点がなければ両座標が一致すると示す。
規約：中間点のない部分では、分離した K 座標は元の対角へ厳密に戻る。
使われ方：対角上の長 Hom を保つ Kan 延長から、標準の全対角を回収する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 最後の対象だけを一、それ以前の二対象を零とするラベル。 -/
def triangleUpperLabel {n : ℕ} (t : Fin (n + 1) →o Fin 3) : Fin (n + 1) →o Fin 2 where
  toFun i := if t i = 2 then 1 else 0
  monotone' := by
    intro i j hij
    have ht := t.monotone hij
    dsimp only
    split_ifs <;> omega

lemma triangleUpperLabel_zero {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) : triangleUpperLabel t i = 0 := by
  simp [triangleUpperLabel, hi]

/-- 中間対象を含まない path では、二つの最大座標が一致する。 -/
lemma triangleTwoCuts_eq_of_no_middle {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (hP : ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (triangleUpperLabel t) (triangleUpperLabel_zero t hi) P =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) P := by
  have hcases : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  apply le_antisymm
  · let k := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (triangleUpperLabel t) (triangleUpperLabel_zero t hi) P
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec (triangleUpperLabel t) (triangleUpperLabel_zero t hi) P
    have hk : ULift.up k ∈ P.I := hm.2
    have hz : (if t k = 2 then (1 : Fin 2) else 0) = 0 := hm.1
    have ht : t k = 0 := by
      rcases hcases (t k) with h | h | h
      · exact h
      · exact False.elim (hP ⟨k, hk, h⟩)
      · rw [h] at hz
        contradiction
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) P k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t ht) hk
  · let k := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) P
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) P
    have hz : (if t k = 0 then (0 : Fin 2) else 1) = 0 := hm.1
    have ht : t k = 0 := by
      by_contra h
      rw [ite_eq_right h] at hz
      contradiction
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero (triangleUpperLabel t) (triangleUpperLabel_zero t hi) P k
      (triangleUpperLabel_zero t ht) hm.2

/-- 中間ラベルが無いときには、その存在を読む標準区間座標は零。 -/
lemma trianglePathMiddle_eq_zero_of_no_middle {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (hP : ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle t P = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle, hP, ite_false]

/-- 中間対象のない全区間では、二つの標準単体への射が全次数で一致する。 -/
lemma triangleCutMaps_eq_of_no_middle {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (hP : ∀ P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j),
      ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap.{u} (triangleUpperLabel t) (triangleUpperLabel_zero t hi) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro l
  exact triangleTwoCuts_eq_of_no_middle t hi (P.obj l) (hP (P.obj l))

/-- 同じ全区間の中間点座標は、直接 path を指定する零端に厳密に定値。 -/
lemma triangleMiddleMap_eq_zero_of_no_middle {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i j : Fin (n + 1)}
    (hP : ∀ P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j),
      ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap.{u} t i j =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro l
  exact trianglePathMiddle_eq_zero_of_no_middle t (P.obj l) (hP (P.obj l))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
