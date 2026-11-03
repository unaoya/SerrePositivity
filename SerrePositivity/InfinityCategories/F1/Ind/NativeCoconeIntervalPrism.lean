module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FatJoinComparison
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeParameterPrism
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationPrism
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationVertex
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：native な指定余錐の標準変換の区間表示は、同じ余錐の円筒制限そのもの。
方針：指定変換頂点の全円柱の式を、右の一点の定値単体で評価する。
規約：余錐・指定頂点・全パラメータを固定する。
使われ方：Yoneda comma の pinched fiber 作用を、同じ密度余錐の元の自然変換へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 指定頂点で正規化した同じ余錐の変換の円柱は、元の join 円柱の制限そのもの。 -/
lemma coconeTransformationPointAt_prism {K X : SSet.{u}} {f : K ⟶ X}
    (c : JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    F2.constantTransformationPrism (SSet.yonedaEquiv.symm
      ((F2.coconeTransformationMap f z).app _ (F2.coconeMappingPointAt c z hv))) =
      joinCylinderMap K Δ[0] ≫ c.val := by
  rw [← SSet.yonedaEquiv_symm_comp, F2.coconeTransformationMap_prism,
    F2.coconeParameterPrism, SSet.yonedaEquiv_symm_comp]
  change joinCylinderMap K Δ[0] ≫ sliceUnderUncurry (SSet.yonedaEquiv.symm c) = _
  rw [sliceUnderUncurry_yoneda]

/-- 元の標準変換の回収ホモトピーは、同じ右 pinched 円筒の元の余錐への像。 -/
lemma coconeTransformationPointAt_interval {K X : SSet.{u}} {f : K ⟶ X}
    (c : JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    rightMappingSpacePrism K ≫ c.val = (β_ Δ[1] K).hom ≫
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex
        ((F2.coconeTransformationMap f z).app _ (F2.coconeMappingPointAt c z hv))).toTruncated).h := by
  have h := (F2.constantTransformationPrism_vertex
    ((F2.coconeTransformationMap f z).app _ (F2.coconeMappingPointAt c z hv))).symm.trans
      (coconeTransformationPointAt_prism c z hv)
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, k⟩
  exact (congrArg (fun q => q.app (Opposite.op ⦋n⦌)
    ((k, t), PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n)) h).symm

end SerrePositivity.InfinityCategories.F2.Ind
