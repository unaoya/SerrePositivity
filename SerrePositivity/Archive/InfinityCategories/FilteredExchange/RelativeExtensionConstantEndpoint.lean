module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningEvaluation

/-!
概要：定値図式を標的とする元の相対終点を、同じ fiber 終点の全評価へ同定する。
方針：同じ全評価の包含が元の延長の同じ制限となることを両側で示す。
規約：相対終点と定値図式の表示を保持。使われ方：元の三角形比較を fiber 比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値標的の相対終点の fiber 表示は、元の同じ fiber 終点評価そのもの。 -/
lemma relativeFunctorExtensionEndpoint_constant_fiber {A D C L : SSet.{u + 1}}
    (b : A ⟶ SpaceInfinity.{u}) (i : D ⟶ A) (v : D ⟶ PointedSpaceInfinity.{u})
    (hv : v ≫ pointedSpaceProjection = i ≫ b)
    (j : C ⟶ A) (a : C ⟶ L) (z : SpaceInfinity.{u} _⦋0⦌)
    (hj : j ≫ b = a ≫ (SSet.const z : L ⟶ SpaceInfinity)) :
    relativeFunctorExtensionEndpoint pointedSpaceProjection b i v hv j (SSet.const z) a hj ≫
        (constantUnstraighteningRelativeIso a z).hom =
      relativeExtensionFiberEndpoint pointedSpaceProjection b i v hv j z
        (hj.trans (SSet.comp_const a z)) := by
  apply uncurry_injective
  apply vertexFiber_hom_ext pointedSpaceProjection z
  rw [constantUnstraighteningRelativeIso_uncurry,
    relativeFunctorExtensionEndpoint_uncurry_fst, relativeExtensionFiberEndpoint_uncurry_ι]

end SerrePositivity.InfinityCategories.F2
