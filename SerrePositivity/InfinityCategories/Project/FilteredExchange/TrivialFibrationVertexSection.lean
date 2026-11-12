module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：自明 Kan 射の切断を、指定した全頂点の持ち上げを保って構成する。
方針：頂点の離散単体集合の単射に対する持ち上げを使う。
規約：頂点上の選択は厳密に保持。使われ方：既存の余極限模型を頂点に持つ余極限関手。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 自明 Kan 射は、全ての指定した頂点の逆像を保つ厳密な切断を持つ。 -/
lemma trivialKanFibration_section_with_vertices {E D : SSet.{u}} (p : E ⟶ D)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (x : D _⦋0⦌ → E _⦋0⦌)
    (hx : ∀ v, p.app (Opposite.op ⦋0⦌) (x v) = v) :
    ∃ s : D ⟶ E, s ≫ p = 𝟙 D ∧ ∀ v, s.app (Opposite.op ⦋0⦌) v = x v := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι D) inferInstance
  have sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι D) p (𝟙 D) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp p (𝟙 D) x hx⟩
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  intro v
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) v
  change sq.lift.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) 0
    at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
