module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HomotopyComponentPrecomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
/-!
概要：右 Kan 輸送の全錐ホモトピーの頂点・図式成分を、元の実単位成分と照合する。
方針：固定頂点と指定図式の全時刻の等式を同じ退化辺で評価し、脚の自然性を使う。
規約：新たな単位の代表は選ばない。使われ方：二つの実極限錐の脚から単位の可逆性を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
variable {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
/-- 保存された右 Kan 輸送の全族を、標準錐から輸送後の錐への同じ実ホモトピーとして読む。 -/
def RightKanConeTransport.wholeHomotopy (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ F₀ F α c) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val t.cone.val where
  h := t.family
  h₀ := t.start
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RightKanConeTransport (wholeHomotopy)

/-- 全時刻で固定された頂点で、右 Kan 輸送の同じ実成分は可逆。 -/
lemma RightKanConeTransport.apexComponent_isInvertible (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ F₀ F α c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge t.wholeHomotopy) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c)
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp t.wholeHomotopy i
  let a := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyComponent_isInvertible_of_fixed H
    (i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val) t.fixedVertex a
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyComponent_precomp_edge t.wholeHomotopy i a
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RightKanConeTransport (apexComponent_isInvertible)

/-- 右 Kan 輸送の図式側の同じ実辺は、元の単位の元の始域での成分そのもの。 -/
lemma RightKanConeTransport.diagramComponent_edge (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ F₀ F α c)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge t.wholeHomotopy v).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c).app (Opposite.op ⦋0⦌) v)).edge := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp t.wholeHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c))
  let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyComponent_edge_of_raw_eq H H' t.diagram v
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyComponent_precomp_edge t.wholeHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c)) v).symm.trans
      (he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyComponent_precomp_edge α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c) v))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RightKanConeTransport (diagramComponent_edge)

/-- 標準錐と輸送後の錐の同じ脚が可逆なら、元の指定単位の同じ実成分も可逆。 -/
lemma RightKanConeTransport.component_isInvertible_of_legs
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ F₀ F α c) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) _⦋0⦌)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c) v))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t.cone v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c).app (Opposite.op ⦋0⦌) v)) := by
  have hA : IsIso (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge t.wholeHomotopy)) := t.apexComponent_isInvertible
  have hL : IsIso (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c) v)) := h₀
  have hR : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t.cone v)) := h₁
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopy_leg_naturality t.wholeHomotopy v
  have hT : IsIso (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c) v) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge t.wholeHomotopy v)) := by
    rw [hn]
    infer_instance
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge t.wholeHomotopy v) :=
    IsIso.of_isIso_comp_left
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c) v))
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge t.wholeHomotopy v))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (t.diagramComponent_edge v)).mp hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RightKanConeTransport (component_isInvertible_of_legs)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
