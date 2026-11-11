module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeFiberPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-! # 相対屋根 prism の共通始点 fiber

概要：底の始端が定値なら、輸送後の境界と全体は同じ fiber 上の厳密な相対問題を与える。
方針：prism の零端を fiber に持ち上げ、比較の正方形を包含後に検証する。
規約：元と商の fiber を混同しない。使われ方：pinched Hom の有限相対充填への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {A K E Q B : SSet.{u}} {i : A ⟶ K} {p : E ⟶ B} {q : Q ⟶ B}
variable {F : E ⟶ Q} {a : A ⟶ E} {g : K ⟶ Q} {β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B}
namespace RoofRelativeFiberPrism
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeFiberPrism i p q F a g β)

/-- 輸送後の元屋根境界。 -/
def sourceZero : A ⟶ E := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ T.source
/-- 輸送後の商屋根の全体。 -/
def targetZero : K ⟶ Q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ T.target

/-- 元屋根境界の射影は同じ指定始点に定値。 -/
lemma sourceZero_over (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    T.sourceZero ≫ p = SSet.const b := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ T.source) ≫ p = _
  rw [Category.assoc, T.source_over, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, hzero, SSet.comp_const]

/-- 商屋根全体の射影も同じ指定始点に定値。 -/
lemma targetZero_over (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    T.targetZero ≫ q = SSet.const b := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ T.target) ≫ q = _
  rw [Category.assoc, T.target_over, hzero]

/-- 元屋根境界を共通始点の実 fiber に回収する。 -/
def sourceFiber (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b T.sourceZero (T.sourceZero_over b hzero)

/-- 商屋根全体を同じ共通始点の実 fiber に回収する。 -/
def targetFiber (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b T.targetZero (T.targetZero_over b hzero)

/-- fiber の元屋根境界を含めると同じ輸送始端に戻る。 -/
lemma sourceFiber_ι (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    T.sourceFiber b hzero ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = T.sourceZero := rfl

/-- fiber の商屋根全体を含めると同じ輸送始端に戻る。 -/
lemma targetFiber_ι (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    T.targetFiber b hzero ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b = T.targetZero := rfl

/-- 輸送した境界と全体は同じ fiber の比較上で厳密に可換。 -/
lemma fiber_square (hF : F ≫ q = p) (b : B _⦋0⦌)
    (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b) :
    T.sourceFiber b hzero ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q F hF b = i ≫ T.targetFiber b hzero := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, T.sourceFiber_ι,
    Category.assoc, T.targetFiber_ι]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ T.source) ≫ F = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ T.target
  rw [Category.assoc, ← T.boundary]
  simpa only [Category.assoc] using
    congrArg (fun r => r ≫ T.target) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0 i)

end RoofRelativeFiberPrism
end SerrePositivity.InfinityCategories.Project.DerivedCategories
