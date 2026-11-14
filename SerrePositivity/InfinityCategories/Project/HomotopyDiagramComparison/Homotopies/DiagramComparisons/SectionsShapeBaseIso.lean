module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FibersBaseIso

/-!
概要：積・cospan・塔の nerve と同型な底に切断の fiber ごとの同値の判定を移す。
方針：底の同型で射影を後合成し、既存の三形状の判定の後で切断の同型を消去する。
規約：全空間の実際の底上の射 f は変更しない。
使われ方：HTT 4.2.4.1 の宇宙を調整した図式での切断比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {K E E' : SSet.{u}}

/-- 概要：離散圏の nerve と同型な底上の fiber ごとの同値は切断空間の同値を誘導する。
方針：離散圏上の判定へ移し、底の同型の前後で切断同値性を移す。
規約：離散対象の型の有限性は要求しない。
使われ方：HTT 4.2.4.1 の豊穣積を調整した底の上で扱う。 -/
lemma simplicialSectionsMap_discreteBaseIso_homotopyEquivalence {J : Type u}
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (e : K ≅ nerve (Discrete J)) (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsMap_homotopyEquivalence_iff_postIso p q e f hf).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_discrete_homotopyEquivalence
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isQCatEquivalence_postIso_all p q e f hf h _

/-- 概要：cospan の nerve と同型な底上の fiber ごとの同値は切断空間の同値を誘導する。
方針：cospan 上の判定へ移し、底の同型で切断同値性を戻す。
規約：f 自身の fibration 性は要求しない。
使われ方：HTT 4.2.4.1 の引き戻しの錐の切断比較。 -/
lemma simplicialSectionsMap_cospanBaseIso_homotopyEquivalence
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (e : K ≅ nerve (AsSmall.{u} WalkingCospan)) (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsMap_homotopyEquivalence_iff_postIso p q e f hf).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_cospan_homotopyEquivalence
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isQCatEquivalence_postIso_all p q e f hf h _

/-- 概要：塔の nerve と同型な底上の fiber ごとの同値は切断空間の同値を誘導する。
方針：自然数の逆順の塔上の判定へ移し、底の同型で切断同値性を戻す。
規約：底の同型は厳密な単体集合の同型として指定する。
使われ方：HTT 4.2.4.1 の塔の錐の切断比較。 -/
lemma simplicialSectionsMap_towerBaseIso_homotopyEquivalence
    (p : E ⟶ K) (q : E' ⟶ K) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (e : K ≅ nerve (AsSmall.{u} ℕᵒᵖ)) (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplicialSectionsMap_homotopyEquivalence_iff_postIso p q e f hf).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_tower_homotopyEquivalence
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isQCatEquivalence_postIso_all p q e f hf h _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
