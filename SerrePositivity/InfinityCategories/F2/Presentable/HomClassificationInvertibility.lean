module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomFiberInvertibility
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningSimplexRestriction

/-!
概要：元の分類比較の評価成分の可逆性を、同じ元の fiber 射の同値性で検出する。
方針：指定された評価自然同型の可換式と、端点の等式による共役を使う。
規約：分類比較そのものを固定し、点ごとに別の同型を選び直さない。
使われ方：全共変 Hom 比較の成分判定と compact 性による生成拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の left fibration 辺を分類して評価した射は、同じ実 fiber 射の同値性を検出。 -/
lemma leftClassificationEdge_evaluation_isIso_iff {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    IsIso ((hoFunctor.map (leftStraighteningInfinityMap B ≫
      evaluateFunctorAt (ULift.up b))).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk
        (leftFibrationInfinityEdge p q f hf).toTruncated)) ↔
          IsQCatEquivalence (vertexFiberMap p q f hf b) := by
  let e := (leftStraighteningInfinityMap_evaluateIso b).toNatIso
  have h := leftClassificationEdge_evaluation_square p q f hf b
  have hi := leftFibrationFiberEvaluation_isIso_iff p q f hf b
  rw [← isIso_comp_right_iff _ (e.hom.app
    (HomotopyCategory.mk (leftFibrationInfinityVertex q)))]
  rw [h, isIso_comp_left_iff]
  exact hi

/-- 元の分類図式間の実際の射は、指定評価で同じ元の fiber 射の同値性を検出。 -/
lemma leftClassificationHom_evaluation_isIso_iff {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    IsIso ((hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
      (leftClassificationHom p q f hf)) ↔ IsQCatEquivalence (vertexFiberMap p q f hf b) := by
  unfold leftClassificationHom
  rw [homMk_edge_ofEq]
  rw [CategoryTheory.Functor.map_comp, isIso_comp_left_iff,
    CategoryTheory.Functor.map_comp, isIso_comp_right_iff]
  exact leftClassificationEdge_evaluation_isIso_iff p q f hf b

end SerrePositivity.InfinityCategories.F2.Presentable
