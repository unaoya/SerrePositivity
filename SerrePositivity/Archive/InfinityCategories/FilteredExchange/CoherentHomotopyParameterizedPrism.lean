module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomotopyVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSimplexPointedStart
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFaces

/-!
概要：元のホモトピーの指定頂点への定値族を、任意の全パラメータの prism へ展開する。
方針：元の辺を厳密に回収し、同じ図式の評価を計算する。
規約：元の円柱を保持。使われ方：三単体の第一辺と選択済みの写像空間作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の追加パラメータで、元の変換頂点の prism は元の円柱の定値族そのもの。 -/
lemma coherentVertexOfHomotopy_parameterizedPrism {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G) :
    functorParameterizedPrism
      (intervalMappingUncurry (SSet.const (coherentVertexOfHomotopy H) : K ⟶ _)) =
      fst (Δ[1] ⊗ B) K ≫ functorSimplexDiagram (curry H.h) := by
  rw [intervalMappingUncurry_const_vertex, coherentVertexOfHomotopy_edge]
  change functorParameterizedPrism (_ ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (curry H.h))) = _
  rw [Equiv.symm_apply_apply]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
