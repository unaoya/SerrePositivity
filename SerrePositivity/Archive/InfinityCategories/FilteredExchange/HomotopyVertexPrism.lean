module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomotopyVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTransformationVertex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：指定辺・指定円柱の頂点表示から、一点パラメータ付きの元の円柱を回収する。
方針：Yoneda と内部 Hom の往復を計算する。
規約：元の代表を保持。使われ方：余極限の指定辺の定値変換との全族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定辺の変換頂点の全区間族は、一点のパラメータを補った元の辺。 -/
lemma intervalMappingUncurry_vertex {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    intervalMappingUncurry (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e)) =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [intervalMappingUncurry, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm
    (functorVertex (SSet.yonedaEquiv.symm e.edge))) = _
  rw [uncurry_yoneda_functorVertex]

/-- 元の定値標的への円柱を coherent 頂点にしても、全円柱の表示は元のまま。 -/
lemma constantTransformationPrism_coherentVertex {K : SSet.{u + 1}}
    {F : K ⟶ SpaceInfinity.{u}} {z : SpaceInfinity.{u} _⦋0⦌}
    (H : SSet.Homotopy F (SSet.const z)) :
    constantTransformationPrism (SSet.yonedaEquiv.symm (coherentVertexOfHomotopy H)) =
      fst (K ⊗ (Δ[1] : SSet.{u + 1})) Δ[0] ≫ H.h := by
  rw [coherentVertexOfHomotopy, constantTransformationPrism_of_edge]
  change _ ≫ (simplicialHomotopyOfFunctorEdge (functorEdgeOfSimplicialHomotopy H)).h = _
  rw [simplicialHomotopyOfFunctorEdge_of_homotopy]

end SerrePositivity.InfinityCategories.F2
