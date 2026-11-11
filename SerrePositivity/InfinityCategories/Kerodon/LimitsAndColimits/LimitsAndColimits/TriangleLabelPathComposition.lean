module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLabelPathCoordinates

/-!
概要：三対象ラベルの座標は、両端の恒等側の合成を無視する。
方針：path の頂点集合の和で中間対象の有無を計算し、既存の最大座標の合成則と合わせる。
規約：中間ラベルを通る合成では、長 Hom の合成端の座標を厳密に選ぶ。
使われ方：制御二胞体の全次数の豊穣合成則。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {n : ℕ} (t : Fin (n + 1) →o Fin 3) {i j k : Fin (n + 1)}
  (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
  (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k))

/-- 零対象の自己 Hom で前合成しても、中間対象の有無は変わらない。 -/
lemma trianglePathMiddle_comp_zero (hj : t j = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle t ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle t Q := by
  classical
  have hP : ¬ ∃ l : Fin (n + 1), ULift.up l ∈ P.I ∧ t l = 1 := by
    rintro ⟨l, hl, ht⟩
    have h := t.monotone (P.le_right _ hl)
    rw [hj, ht] at h
    omega
  have h : (∃ l : Fin (n + 1), ULift.up l ∈ P.I ∪ Q.I ∧ t l = 1) ↔
      (∃ l : Fin (n + 1), ULift.up l ∈ Q.I ∧ t l = 1) := by
    constructor
    · rintro ⟨l, hl | hl, ht⟩
      · exact False.elim (hP ⟨l, hl, ht⟩)
      · exact ⟨l, hl, ht⟩
    · rintro ⟨l, hl, ht⟩
      exact ⟨l, Or.inr hl, ht⟩
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle, compFunctor_obj, SimplicialThickening.comp_I, h]

/-- 終対象の自己 Hom で後合成しても、中間対象の有無は変わらない。 -/
lemma trianglePathMiddle_comp_two (hj : t j = 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle t ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle t P := by
  classical
  have hQ : ¬ ∃ l : Fin (n + 1), ULift.up l ∈ Q.I ∧ t l = 1 := by
    rintro ⟨l, hl, ht⟩
    have h := t.monotone (Q.left_le _ hl)
    rw [hj, ht] at h
    omega
  have h : (∃ l : Fin (n + 1), ULift.up l ∈ P.I ∪ Q.I ∧ t l = 1) ↔
      (∃ l : Fin (n + 1), ULift.up l ∈ P.I ∧ t l = 1) := by
    constructor
    · rintro ⟨l, hl | hl, ht⟩
      · exact ⟨l, hl, ht⟩
      · exact False.elim (hQ ⟨l, hl, ht⟩)
    · rintro ⟨l, hl, ht⟩
      exact ⟨l, Or.inl hl, ht⟩
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle, compFunctor_obj, SimplicialThickening.comp_I, h]

/-- 中間対象を通る合成は、長 Hom の合成端の座標を選ぶ。 -/
lemma trianglePathMiddle_comp_one (hj : t j = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle t ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) = 1 := by
  classical
  exact if_pos ⟨j, Or.inl P.right, hj⟩

/-- 零対象の自己 Hom での前合成は、二つの座標をともに保存する。 -/
lemma triangleLabelPathCoordinates_comp_zero (hi : t i = 0) (hj : t j = 0) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates t hi k =
      snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates t hj k := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro l
    exact trianglePathMiddle_comp_zero t (P.obj l) (Q.obj l) hj
  · apply stdSimplex.ext
    intro l
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_comp_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hj) (P.obj l) (Q.obj l)

/-- 終対象の自己 Hom での後合成も、二つの座標をともに保存する。 -/
lemma triangleLabelPathCoordinates_comp_two (hi : t i = 0) (hj : t j = 2) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates t hi k =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates t hi j := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro l
    exact trianglePathMiddle_comp_two t (P.obj l) (Q.obj l) hj
  · apply stdSimplex.ext
    intro l
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_comp_one (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel, hj]) (P.obj l) (Q.obj l)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
