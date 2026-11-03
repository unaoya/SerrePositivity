module
public import SerrePositivity.InfinityCategories.Derived.HomotopyComponentPrecomp
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Definition
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.ConeHomotopyEdges
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
variable {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
/-- 保存された右 Kan 輸送の全族を、標準錐から輸送後の錐への同じ実ホモトピーとして読む。 -/
def RightKanConeTransport.wholeHomotopy (t : RightKanConeTransport δ F₀ F α c) :
    SSet.Homotopy (rightKanCanonicalCone δ F c).val t.cone.val where
  h := t.family
  h₀ := t.start
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property
/-- 全時刻で固定された頂点で、右 Kan 輸送の同じ実成分は可逆。 -/
lemma RightKanConeTransport.apexComponent_isInvertible (t : RightKanConeTransport δ F₀ F α c) :
    IsInvertibleEdge (F2.coneHomotopyApexEdge t.wholeHomotopy) := by
  let i := joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)
  let H := functorHomotopyPrecomp t.wholeHomotopy i
  let a := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hi := homotopyComponent_isInvertible_of_fixed H
    (i ≫ (rightKanCanonicalCone δ F c).val) t.fixedVertex a
  have he := homotopyComponent_precomp_edge t.wholeHomotopy i a
  exact (isInvertibleEdge_congr he).mp hi
/-- 右 Kan 輸送の図式側の同じ実辺は、元の単位の元の始域での成分そのもの。 -/
lemma RightKanConeTransport.diagramComponent_edge (t : RightKanConeTransport δ F₀ F α c)
    (v : (rightKanShape δ c) _⦋0⦌) :
    (F2.coneHomotopyDiagramEdge t.wholeHomotopy v).edge =
      (simplicialHomotopyVertexEdge α ((rightKanProjection δ c).app (Opposite.op ⦋0⦌) v)).edge := by
  let H := functorHomotopyPrecomp t.wholeHomotopy (joinInr Δ[0] (rightKanShape δ c))
  let H' := functorHomotopyPrecomp α (rightKanProjection δ c)
  have he := homotopyComponent_edge_of_raw_eq H H' t.diagram v
  exact (homotopyComponent_precomp_edge t.wholeHomotopy
    (joinInr Δ[0] (rightKanShape δ c)) v).symm.trans
      (he.trans (homotopyComponent_precomp_edge α (rightKanProjection δ c) v))
/-- 標準錐と輸送後の錐の同じ脚が可逆なら、元の指定単位の同じ実成分も可逆。 -/
lemma RightKanConeTransport.component_isInvertible_of_legs
    (t : RightKanConeTransport δ F₀ F α c) (v : (rightKanShape δ c) _⦋0⦌)
    (h₀ : IsInvertibleEdge (F2.nativeConeLeg (rightKanCanonicalCone δ F c) v))
    (h₁ : IsInvertibleEdge (F2.nativeConeLeg t.cone v)) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge α ((rightKanProjection δ c).app (Opposite.op ⦋0⦌) v)) := by
  have hA : IsIso (Truncated.HomotopyCategory.homMk
      (F2.coneHomotopyApexEdge t.wholeHomotopy)) := t.apexComponent_isInvertible
  have hL : IsIso (Truncated.HomotopyCategory.homMk
      (F2.nativeConeLeg (rightKanCanonicalCone δ F c) v)) := h₀
  have hR : IsIso (Truncated.HomotopyCategory.homMk (F2.nativeConeLeg t.cone v)) := h₁
  have hn := F2.coneHomotopy_leg_naturality t.wholeHomotopy v
  have hT : IsIso (Truncated.HomotopyCategory.homMk
      (F2.nativeConeLeg (rightKanCanonicalCone δ F c) v) ≫
        Truncated.HomotopyCategory.homMk (F2.coneHomotopyDiagramEdge t.wholeHomotopy v)) := by
    rw [hn]
    infer_instance
  have hi : IsInvertibleEdge (F2.coneHomotopyDiagramEdge t.wholeHomotopy v) :=
    IsIso.of_isIso_comp_left
      (Truncated.HomotopyCategory.homMk (F2.nativeConeLeg (rightKanCanonicalCone δ F c) v))
      (Truncated.HomotopyCategory.homMk (F2.coneHomotopyDiagramEdge t.wholeHomotopy v))
  exact (isInvertibleEdge_congr (t.diagramComponent_edge v)).mp hi
end SerrePositivity.InfinityCategories
