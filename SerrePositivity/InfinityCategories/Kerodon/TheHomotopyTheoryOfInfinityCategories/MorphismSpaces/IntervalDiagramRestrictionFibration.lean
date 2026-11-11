module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanEquivalenceLiftingFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramColimitCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：底の単射に沿う、元の両端固定の区間 Hom の制限は Kan fibration。
方針：前合成の同値持ち上げを同じ区間 Hom の後合成へ移し、Kan 性を使う。
規約：単射自身の同値性やモデル圏の追加仮定を要求しない。
使われ方：元の分類主写像の Hom 比較のセル・骨格による降下。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 同値を右に持ち上げる同じ射は、両端固定の区間 Hom の Kan fibration を与える。 -/
lemma intervalMappingPostOfEq_fibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : p.app _ x = x') (hy : p.app _ y = y') :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y hx hy) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanEquivalenceLifting_intervalMappingPostOfEq p hp x y hx hy)

/-- 底の任意の単射に沿う同じ区間 Hom の制限は、全ホーンを持ち上げる。 -/
lemma intervalDiagramRestriction_fibration {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (F G : B ⟶ X) : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction i F G) :=
  intervalMappingPostOfEq_fibration ((pre i).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre i) _ _ _ _

/-- 底上の同じ単射に沿う、端点を正規化した区間 Hom の制限も Kan fibration。 -/
lemma intervalDiagramOverPre_fibration {B X : SSet.{u}} [Quasicategory X]
    (F G : B ⟶ X) {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G i) :=
  intervalMappingPostOfEq_fibration ((pre i.left).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre i.left) _ _ _ _

/-- 同じ区間 Hom の降下図式の、単射に沿う実際の遷移は Kan fibration。 -/
lemma intervalDiagramOverFunctor_map_fibration {B X : SSet.{u}} [Quasicategory X]
    (F G : B ⟶ X) {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor F G).map i.op) :=
  intervalDiagramOverPre_fibration F G i

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
