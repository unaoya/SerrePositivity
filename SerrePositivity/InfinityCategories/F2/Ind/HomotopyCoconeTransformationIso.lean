module

public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyTransformationVertex
public import SerrePositivity.InfinityCategories.F2.CoconeRealizationTransformation
public import SerrePositivity.InfinityCategories.F2.YonedaHomotopyVertex

/-!
概要：任意の指定円柱の native 余錐実現の標準変換を、その同じ指定変換へ比較する。
方針：区間模型から元の円柱への厳密な回収を用い、既存の実現比較を移す。
規約：実現済みの余錐を選び直さない。使われ方：Indκ の指定係数余錐の評価比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ任意の全円柱を実現した native 余錐の標準変換は、元の指定変換と同型。 -/
def homotopyCoconeTransformationIso {K X : SSet.{u}} [Quasicategory X]
    {f : K ⟶ X} {z : X _⦋0⦌} (H : SSet.Homotopy f (SSet.const z))
    (R : F2.HomotopyCoconeRealization H) :
    VertexIso ((F2.coconeTransformationMap f z).app (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt R.cocone z R.vertex_eq)) (homotopyTransformationVertex H) := by
  have hh : (simplicialHomotopyOfFunctorEdge
      (intervalMappingEdgeOfVertex (homotopyTransformationVertex H)).toTruncated) = H := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact homotopyTransformationVertex_h H
  have he : ∀ R' : F2.HomotopyCoconeRealization (simplicialHomotopyOfFunctorEdge
      (intervalMappingEdgeOfVertex (homotopyTransformationVertex H)).toTruncated),
      VertexIso ((F2.coconeTransformationMap f z).app (Opposite.op ⦋0⦌)
        (F2.coconeMappingPointAt R'.cocone z R'.vertex_eq)) (homotopyTransformationVertex H) :=
    fun R' ↦ F2.vertexIsoOfYonedaHomotopy
      (F2.coconeRealizationTransformationHomotopy (homotopyTransformationVertex H) R')
  rw [hh] at he
  exact he R

end SerrePositivity.InfinityCategories.F2.Ind
