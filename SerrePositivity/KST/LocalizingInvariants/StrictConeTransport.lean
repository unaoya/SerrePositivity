module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.F2.CatInfinity.SpecifiedConeTransportRestrictions
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Core.CatInfinity.HomotopyVerticalRestriction

/-!
概要：通常の自然変換の元の円柱を保持する、coherent 極限錐の輸送。
方針：F2 の指定 prism の輸送と成分の計算を用いる。
規約：頂点・図式の両方で元の辺を追跡する。使われ方：K-5 の fiber 包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants.StrictConeTransport

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] [Quasicategory (SimplicialNerve C)]
  {F G : I ⥤ C} (η : F ⟶ G)
  (hη : ∀ i, IsInvertibleEdge (coherentNerveEdge (η.app i)))
  (d : JoinCone (strictCoherentDiagram G)) (hd : IsLimitCone d)

/-- 元の通常の自然変換の指定 prism を保持する極限錐の輸送。 -/
def transport : F2.SpecifiedLimitConeTransport (p := strictCoherentDiagram F)
    (F2.strictCoherentNatTransMap η) d :=
  F2.specifiedLimitConeTransport (F2.strictCoherentNatTransMap η)
    (F2.strictCoherentNatTransMap_zero η) (F2.strictCoherentNatTransMap_one η)
    (F2.strictCoherentNatTransMap_vertical_isInvertible η hη) d hd

/-- 輸送の頂点の比較辺は、比較先の頂点の定値辺。 -/
lemma apexEdge :
    (F2.coneHomotopyApexEdge (transport η hη d hd).homotopy).edge =
      PinchedHom.constant d.vertex 1 := by
  let J := (SSet.uliftFunctor.{v, u}).obj (nerve I)
  have h := F2.homotopyVertexEdge_constant (transport η hη d hd).homotopy
    (joinInl Δ[0] J) (joinInl Δ[0] J ≫ d.val)
    (transport η hη d hd).apex (SSet.yonedaEquiv (𝟙 Δ[0]))
  exact h

/-- 輸送の図式辺は元の自然変換の同じ成分の辺。 -/
lemma diagramEdge (i : I) :
    (F2.coneHomotopyDiagramEdge (transport η hη d hd).homotopy
      (ULift.up (ComposableArrows.mk₀ i))).edge = (coherentNerveEdge (η.app i)).edge := by
  let J := (SSet.uliftFunctor.{v, u}).obj (nerve I)
  have h := F2.homotopyVertexEdge_prism (transport η hη d hd).homotopy
    (joinInr Δ[0] J) (F2.strictCoherentNatTransMap η)
    (transport η hη d hd).diagram (ULift.up (ComposableArrows.mk₀ i))
  exact h.trans (F2.strictCoherentNatTransMap_component η i)

end SerrePositivity.KST.LocalizingInvariants.StrictConeTransport
