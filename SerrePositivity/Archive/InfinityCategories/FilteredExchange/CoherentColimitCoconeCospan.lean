module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitCoconeTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorCospanCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：元の二三角形からなる全 cospan 錐を、元の native 余錐の全錐へ写す。
方針：余錐選択の関手で全形状を写し、二三角形・底・頂点を照合する。
規約：共通対角辺と全二単体を保持。使われ方：a6 の native 出力との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F X} {b : SSet.Homotopy F Y}
  {f : SSet.Homotopy X Z} {g : SSet.Homotopy Y Z} {d : SSet.Homotopy F Z}
  (L : FunctorCompositionTriangle a f d) (R : FunctorCompositionTriangle b g d)

/-- 元の native 余錐を頂点に持つ、元の全 cospan 錐の持ち上げ。 -/
def coherentColimitCoconeCospan :=
  mapJoinCone (coherentColimitCoconeFunctor B) (functorCospanCone L R)

/-- 左二単体は、元の指定三角形の余錐への持ち上げそのもの。 -/
lemma coherentColimitCoconeCospan_left :
    cospanConeTriangleLeft ≫ (coherentColimitCoconeCospan B L R).val =
      (coherentColimitCoconeTriangle B L).diagram := by
  change cospanConeTriangleLeft ≫
    (functorCospanConeDiagram L R ≫ coherentColimitCoconeFunctor B) = _
  rw [← Category.assoc, functorCospanConeDiagram_left]
  rfl

/-- 右二単体も同じ共通対角辺を持つ元の持ち上げ。 -/
lemma coherentColimitCoconeCospan_right :
    cospanConeTriangleRight ≫ (coherentColimitCoconeCospan B L R).val =
      (coherentColimitCoconeTriangle B R).diagram := by
  change cospanConeTriangleRight ≫
    (functorCospanConeDiagram L R ≫ coherentColimitCoconeFunctor B) = _
  rw [← Category.assoc, functorCospanConeDiagram_right]
  rfl

/-- 図式への制限は、元の二三角形から貼った全錐を厳密に回収する。 -/
lemma coherentColimitCoconeCospan_restrict :
    (coherentColimitCoconeCospan B L R).val ≫ coconeRestriction _ _ =
      (functorCospanCone L R).val := by
  change ((functorCospanCone L R).val ≫ coherentColimitCoconeFunctor B) ≫ _ = _
  rw [Category.assoc, coherentColimitCoconeFunctor_restrict, Category.comp_id]

/-- 持ち上げた全錐の頂点は、元の入力 F の native な全空間余錐。 -/
lemma coherentColimitCoconeCospan_vertex :
    (coherentColimitCoconeCospan B L R).vertex =
      functorVertex (coherentDiagramTotalCocone F).val := by
  rw [coherentColimitCoconeCospan, mapJoinCone_vertex, functorCospanCone_vertex,
    coherentColimitCoconeFunctor_vertex]

/-- 全余錐の頂点で評価した全錐は、元の全錐への余極限関手の像。 -/
lemma coherentColimitCoconeCospan_apex :
    (coherentColimitCoconeCospan B L R).val ≫ evaluateFunctorAt
      (SSet.yonedaEquiv (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1}))) =
      (mapJoinCone (coherentColimitFunctor B) (functorCospanCone L R)).val := by
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2
