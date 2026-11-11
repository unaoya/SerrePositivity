module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniversalConeChoiceProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PointedConeLeftFibration

/-!
概要：普遍錐の選択を忘れ、全零隅四角形の始対象を得る。
方針：元の実引き戻しの同型と同じ頂点 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ固定頂点を保つ錐の比較 `vertexFiberMap_innerFibration`。 -/
instance vertexFiberMap_innerFibration {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    [InnerFibration f] (x : B _⦋0⦌) : InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf x) where
  mem := by
    intro A D i hi
    have := InnerFibration.mem (q := f) i hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_hasLiftingProperty p q f hf x i

/-- 同じ固定頂点を保つ錐の比較 `coneInputSourceFiber_quasicategory`。 -/
instance coneInputSourceFiber_quasicategory {A K X : SSet.{u}} [Quasicategory X]
    (p : A ⟶ (ihom K).obj X) [InnerFibration p] (x : X _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x) := by
  have : InnerFibration (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p) :=
    ⟨innerFibrations.of_isPullback (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p).flip
      (InnerFibration.mem (q := p))⟩
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection K X x)
  exact quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p) rfl x)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
