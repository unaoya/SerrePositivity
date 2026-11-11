module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StrictIntervalMappingSimplex

/-!
概要：二点の図式間の同じ二つの成分の族を、全次数で strict 変換の族へ復元する。
方針：交差射の可換式を各単体で使い、元の成分の自然性を保持する。
規約：全パラメーターを保ち、各成分を厳密に回収する。
使われ方：一次元セルの変換空間の pullback の普遍性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable (F G : ULift.{u} (Fin 2) ⥤ SSet.{u}) {T : SSet.{u}}
  (a : T ⟶ (ihom (F.obj (ULift.up 0))).obj (G.obj (ULift.up 0)))
  (b : T ⟶ (ihom (F.obj (ULift.up 1))).obj (G.obj (ULift.up 1)))
  (h : a ≫ (ihom (F.obj (ULift.up 0))).map (G.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow) =
    b ≫ (pre (F.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).app (G.obj (ULift.up 1)))

/-- 元の二成分の整合する族を、同じ strict 変換の全パラメーターの族へ復元する。 -/
def strictIntervalMappingLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G where
  app n := ↾fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.strictIntervalMappingSimplex F G n (a.app n x) (b.app n x)
    (ConcreteCategory.congr_hom (NatTrans.congr_app h n) x)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · exact a.naturality_apply α x
    · exact b.naturality_apply α x

/-- 復元した同じ変換の零成分は元の零成分の族。 -/
lemma strictIntervalMappingLift_zero :
    strictIntervalMappingLift F G a b h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 0) = a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 復元した同じ変換の一成分は元の一成分の族。 -/
lemma strictIntervalMappingLift_one :
    strictIntervalMappingLift F G a b h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 1) = b := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の二つの成分評価は、全パラメーターの strict 変換を一意に決める。 -/
lemma strictIntervalMapping_hom_ext (m n : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G)
    (h₀ : m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 0) =
      n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 0))
    (h₁ : m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 1) =
      n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 1)) : m = n := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  funext i
  rcases i with ⟨i⟩
  fin_cases i
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₀ d) x
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁ d) x

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
