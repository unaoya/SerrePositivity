module

public import SerrePositivity.KST.LocalizingInvariants.FiberConeHomotopyUniqueness
public import SerrePositivity.KST.LocalizingInvariants.FullyFaithfulIsoTransport

/-!
概要：指定した底図式の同型を、同じ底比較の類を持つ実極限錐の全同型へ持ち上げる。
方針：普遍錐の図式射影の充満忠実性を使い、指定した同型の逆像を包含で戻す。
規約：相対条件を構成データに保持。使われ方：fiber 正方形の右辺固定比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberCone

variable {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q)

structure RelativeDiagramIso where
  iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val
  base_arrow : Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K) iso.hom) = Arrow.mk e.hom

lemma projectionVertex_eq : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X)).toFunctor.obj
    (HomotopyCategory.mk (vertex c hc)) = HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  change HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ c.val)) = _
  exact congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) c.property

def relativeDiagramIso : RelativeDiagramIso c d e := by
  let T := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X)).toFunctor
  let hx := projectionVertex_eq c hc
  let hy := projectionVertex_eq d hd
  let a := transportedPreimageIso T (projectionHoFullyFaithful K X) hx hy e
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).ι
  let E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val := (hoFunctor.map i).toFunctor.mapIso a
  refine ⟨E, ?_⟩
  change Arrow.mk (((hoFunctor.map i).toFunctor ⋙
    (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X)).toFunctor).map a.hom) = _
  rw [← Cat.Hom.comp_toFunctor, ← hoFunctor.map_comp]
  change Arrow.mk (T.map a.hom) = _
  exact transportedPreimageIso_map_arrow T (projectionHoFullyFaithful K X) hx hy e

end SerrePositivity.KST.LocalizingInvariants.FiberCone
