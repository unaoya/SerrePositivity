module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyFunctorProduct
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeConeFamilyEvaluation
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：元の関手族上の任意の元の極限錐を、元の反復積関手の全錐へ比較する。
方針：元の slice 内の終対象の一意性を使い、全錐と頂点関手への両作用を保持する。
規約：元の比較元の全錐と元の底図式を保持。元の錐の極限性は明示的な証明を要求する。
使われ方：各前層で評価した元の極限錐の族と sifted 積比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G)) (hc : IsLimitCone c)

/-- 元の関手図式上の元の極限錐と、元の反復積全錐の、同じ slice 内の比較。 -/
def finiteFamilyFunctorProductConeComparison :
    VertexIso (X := sliceOver (finiteFamilyFunctorDiagram G)) c
      (finiteFamilyFunctorProductCone G) :=
  terminalVertexIso hc (finiteFamilyFunctorProductCone_isLimit G)

/-- 元の slice 比較は、元の全錐の全関手の間の同型を与える。 -/
def finiteFamilyFunctorProductWholeConeIso :
    FunctorIso c.val (finiteFamilyFunctorProductCone G).val := by
  have e := (finiteFamilyFunctorProductConeComparison G c hc).map
    (nativeConeFunctorFamily (finiteFamilyFunctorDiagram G))
  rw [nativeConeFunctorFamily_vertex, nativeConeFunctorFamily_vertex] at e
  exact e

/-- 元の全錐の頂点関手は、元の反復積関手と coherent に同型。 -/
def finiteFamilyFunctorProductApexIso
    (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hA : c.vertex = functorVertex A) : FunctorIso A (finiteFamilyCoherentProduct G) := by
  have e := (finiteFamilyFunctorProductConeComparison G c hc).map
    (sliceOverProjection (finiteFamilyFunctorDiagram G))
  change VertexIso c.vertex (finiteFamilyFunctorProductCone G).vertex at e
  rw [hA, finiteFamilyFunctorProductCone_vertex] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
