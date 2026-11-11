module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-! # 相対普遍性の合成と比較
概要：相対始点・終点境界充填を合成し、固定された基底上の普遍頂点を比較する。
方針：基底と元の二段階で境界を充填し、fiber の始対象の一意性を使う。
規約：合成には quasicategory 性を要求しない。使われ方：二方向の余極限補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：相対始点境界充填は合成する。
方針：先に中間の境界を充填し、その充填を基底として元で充填する。
規約：追加の存在・fibration 仮定なし。使われ方：反復余極限の普遍性。 -/
lemma InitialBoundaryLifting.comp {E B D : SSet.{u}} (p : E ⟶ B) (q : B ⟶ D)
    {x : E _⦋0⦌} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting q (p.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (p ≫ q) x := by
  intro n a b ha sq
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ p) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  obtain ⟨M, hM, hMq⟩ := hq n (a ≫ p) b hfirst ⟨by simpa only [Category.assoc] using sq.w⟩
  obtain ⟨F, hF, hFp⟩ := hp n a M ha ⟨hM.symm⟩
  exact ⟨F, hF, by rw [← Category.assoc, hFp, hMq]⟩

/-- 概要：相対終点境界充填は合成する。
方針：中間と元の順で指定した終点を保って境界を充填する。
規約：追加の存在・fibration 仮定なし。使われ方：双対の反復極限。 -/
lemma TerminalBoundaryLifting.comp {E B D : SSet.{u}} (p : E ⟶ B) (q : B ⟶ D)
    {x : E _⦋0⦌} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting q (p.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (p ≫ q) x := by
  intro n a b ha sq
  have hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ p) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  obtain ⟨M, hM, hMq⟩ := hq n (a ≫ p) b hlast ⟨by simpa only [Category.assoc] using sq.w⟩
  obtain ⟨F, hF, hFp⟩ := hp n a M ha ⟨hM.symm⟩
  exact ⟨F, hF, by rw [← Category.assoc, hFp, hMq]⟩

/-- 概要：同じ基底の上の二つの相対始対象は元の quasicategory で同型。
方針：fiber の始対象として比較してから包含で写す。
規約：p は inner fibration。使われ方：二通りの普遍補完の比較。 -/
def relativeInitialVertexIso {E B : SSet.{u}} [Quasicategory E]
    (p : E ⟶ B) [InnerFibration p] {x y : E _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p y)
    (hxy : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y := by
  let b := p.app (Opposite.op ⦋0⦌) x
  let a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨x, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b).symm⟩
  let c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨y, hxy.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b).symm⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting.isInitialVertex_fiber p b a hx)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting.isInitialVertex_fiber p b c hy)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)

end SerrePositivity.KST.SConstruction
