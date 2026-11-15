module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：元の切断空間の全パラメーターを、同じ底の指定頂点のfiberで評価する。
方針：元の普遍切断を底の定値頂点で制限し、指定fiberへ持ち上げる。
規約：IS-W2 R02〜R03の既存の評価・後合成則。充填性を仮定しない。
使われ方：同じBK点とnative錐の脚を、共通の復元のfiberで照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {E F B : SSet.{u}}

/-- 元の普遍切断を、同じ底の指定頂点のfiberで評価する。 -/
def simplicialSectionsFiberEvaluation (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSections p ⟶ vertexFiber p b :=
  vertexFiberLift p b
    (lift (SSet.const b) (𝟙 (simplicialSections p)) ≫ simplicialSectionsEvaluation p) (by
      rw [Category.assoc, simplicialSectionsEvaluation_projection, lift_fst])

/-- fiberの包含で戻すと、元の同じ普遍切断の評価そのもの。 -/
@[reassoc] theorem simplicialSectionsFiberEvaluation_ι (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSectionsFiberEvaluation p b ≫ vertexFiberι p b =
      lift (SSet.const b) (𝟙 (simplicialSections p)) ≫ simplicialSectionsEvaluation p := rfl

/-- 元の切断の後合成は、同じfiberでの評価と厳密に可換。 -/
theorem simplicialSectionsFiberEvaluation_naturality
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    simplicialSectionsMap f hf ≫ simplicialSectionsFiberEvaluation q b =
      simplicialSectionsFiberEvaluation p b ≫ vertexFiberMap p q f hf b := by
  apply vertexFiber_hom_ext q b
  rw [Category.assoc, simplicialSectionsFiberEvaluation_ι, ← Category.assoc]
  have ht : simplicialSectionsMap f hf ≫
      lift (SSet.const b) (𝟙 (simplicialSections q)) =
    lift (SSet.const b) (𝟙 (simplicialSections p)) ≫ (B ◁ simplicialSectionsMap f hf) := rfl
  rw [ht, Category.assoc, simplicialSectionsMap_evaluation,
    Category.assoc, vertexFiberMap_ι, simplicialSectionsFiberEvaluation_ι_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
