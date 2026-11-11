module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialHomComparison

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationFamilyExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
概要：同じ評価を持つ二つの実際の Hom 比較円柱を、二辺を保つ一つの三角形で結ぶ。
方針：共通始点の二円柱を零番目ホーン上に貼り、評価固定の族の延長を適用する。
規約：両円柱の raw な射を指定する。第三辺だけのホモトピー存在命題へ落とさない。
使われ方：共通 end の制限比較と元の三角形・四面体の全 Hom の族との高次照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
private lemma sourceFace (X : SSet.{u}) :
    X ◁ stdSimplex.δ (1 : Fin 2) = fst X (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro k
    have ht : t k = 0 := Fin.eq_zero (t k)
    change (SimplexCategory.δ (1 : Fin 2)).toOrderHom (t k) = 0
    rw [ht]
    rfl

private lemma thirdSource (X : SSet.{u}) :
    SSet.ι₀ ≫ (X ◁ stdSimplex.δ (0 : Fin 3)) =
      SSet.ι₁ ≫ (X ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro k
    rfl

private lemma thirdTarget (X : SSet.{u}) :
    SSet.ι₁ ≫ (X ◁ stdSimplex.δ (0 : Fin 3)) =
      SSet.ι₁ ≫ (X ◁ stdSimplex.δ (1 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro k
    rfl

variable {E B T : SSet.{u}} (q : E ⟶ B) (c : E _⦋0⦌) (y : B _⦋0⦌)
  (v : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q y) {s a b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y}
  (H₀ : SSet.Homotopy s a) (H₁ : SSet.Homotopy s b)

/-- 指定した一つの終点の族を評価として保つ、実際の中間 Hom 比較円柱。 -/
structure InitialEvaluationCylinder (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
    (l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y) where
  homotopy : SSet.Homotopy (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection q c hc y) l
  evaluation : homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T Δ[1] ≫ v

/-- 指定した中間 Hom の族を、元の評価を保って始対象の切断と比較する。 -/
def initialEvaluationCylinder (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) (l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y)
    (hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = v) :
    InitialEvaluationCylinder q c y v hc l :=
  Classical.choice (by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation_trivialKanFibration q c hc y
    obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y) (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection q c hc y) l
      (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection_evaluation, Category.comp_id, hl])
    exact ⟨⟨H, by simpa only [Category.assoc, hl] using hH⟩⟩)

/-- 指定した二円柱を二辺として持ち、同じ終点評価を保つ実際の三角形。 -/
structure InitialEvaluationHomotopyTriangle where
  family : T ⊗ (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q c y
  first : (T ◁ stdSimplex.δ (2 : Fin 3)) ≫ family = H₀.h
  diagonal : (T ◁ stdSimplex.δ (1 : Fin 3)) ≫ family = H₁.h
  evaluation : family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T (Δ[2] : SSet.{u}) ≫ v

/-- 二つの元の比較円柱を固定したまま、同じ評価上で三角形を充填する。 -/
def initialEvaluationHomotopyTriangle (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
    (h₀ : H₀.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T (Δ[1] : SSet.{u}) ≫ v)
    (h₁ : H₁.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T (Δ[1] : SSet.{u}) ≫ v) :
    InitialEvaluationHomotopyTriangle q c y v H₀ H₁ :=
  Classical.choice (by
    let po := horn₂₀.isPushout.map (tensorLeft T)
    have hz : (T ◁ stdSimplex.δ (1 : Fin 2)) ≫ H₀.h =
        (T ◁ stdSimplex.δ (1 : Fin 2)) ≫ H₁.h := by
      have hi : (T ◁ stdSimplex.δ (1 : Fin 2)) =
          fst T (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := sourceFace T
      rw [hi, Category.assoc, Category.assoc, H₀.h₀, H₁.h₀]
    let W := po.desc H₀.h H₁.h hz
    have hleft : (T ◁ horn₂₀.ι₀₁) ≫ W = H₀.h := po.inl_desc _ _ _
    have hright : (T ◁ horn₂₀.ι₀₂) ≫ W = H₁.h := po.inr_desc _ _ _
    have hW : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T (horn 2 0) ≫ v := by
      apply po.hom_ext
      · change (T ◁ horn₂₀.ι₀₁) ≫ (W ≫ _) = (T ◁ horn₂₀.ι₀₁) ≫ _
        rw [← Category.assoc, hleft, h₀, ← Category.assoc, whiskerLeft_fst]
      · change (T ◁ horn₂₀.ι₀₂) ≫ (W ≫ _) = (T ◁ horn₂₀.ι₀₂) ≫ _
        rw [← Category.assoc, hright, h₁, ← Category.assoc, whiskerLeft_fst]
    obtain ⟨U, hU, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_initialEvaluationFamily_of_mono q c hc y v (horn 2 0).ι W hW
    refine ⟨⟨U, ?_, ?_, hU⟩⟩
    · have h := congrArg (fun k ↦ (T ◁ horn₂₀.ι₀₁) ≫ k) hb
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, horn.ι_ι] at h
      exact h.trans hleft
    · have h := congrArg (fun k ↦ (T ◁ horn₂₀.ι₀₂) ≫ k) hb
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, horn.ι_ι] at h
      exact h.trans hright)

variable (D : InitialEvaluationHomotopyTriangle q c y v H₀ H₁)

/-- 同じ三角形の第三辺は、元の両円柱の終点を結ぶ実際のホモトピー。 -/
def initialEvaluationHomotopyTriangleThird : SSet.Homotopy a b where
  h := (T ◁ stdSimplex.δ (0 : Fin 3)) ≫ D.family
  h₀ := by
    change SSet.ι₀ ≫ ((T ◁ stdSimplex.δ (0 : Fin 3)) ≫ D.family) = a
    have hi : SSet.ι₀ ≫ (T ◁ stdSimplex.δ (0 : Fin 3)) =
        SSet.ι₁ ≫ (T ◁ stdSimplex.δ (2 : Fin 3)) := thirdSource T
    rw [← Category.assoc, hi, Category.assoc, D.first]
    exact H₀.h₁
  h₁ := by
    change SSet.ι₁ ≫ ((T ◁ stdSimplex.δ (0 : Fin 3)) ≫ D.family) = b
    have hi : SSet.ι₁ ≫ (T ◁ stdSimplex.δ (0 : Fin 3)) =
        SSet.ι₁ ≫ (T ◁ stdSimplex.δ (1 : Fin 3)) := thirdTarget T
    rw [← Category.assoc, hi, Category.assoc, D.diagonal]
    exact H₁.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 第三辺も、同じ評価を全時刻で固定する。 -/
lemma initialEvaluationHomotopyTriangleThird_evaluation :
    (initialEvaluationHomotopyTriangleThird q c y v H₀ H₁ D).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T (Δ[1] : SSet.{u}) ≫ v := by
  rw [initialEvaluationHomotopyTriangleThird, Category.assoc, D.evaluation,
    ← Category.assoc, whiskerLeft_fst]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
