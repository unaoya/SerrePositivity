module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversalCommaSection
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantUnitFormula

/-!
概要：comma の coherent な切断から、標的関手と元の円柱による単位を構成する。
方針：始域の切断条件でホモトピーの始点を正規化し、その同じ辺の類を取る。
規約：単位の各成分は元の円柱の頂点辺の類。随伴性は別に証明する。
使われ方：各点の局所置換から coherent な反射の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 始域の切断条件で正規化した、元の comma の円柱そのものによる単位。 -/
def commaSectionUnitHomotopy {X Y : SSet.{u}} (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X) :
    SSet.Homotopy (𝟙 X) ((s ≫ unitCommaTarget G) ≫ G) where
  h := (unitCommaHomotopy s).h
  h₀ := by
    rw [(unitCommaHomotopy s).h₀, hs]
    rfl
  h₁ := (unitCommaHomotopy s).h₁
  rel := (unitCommaHomotopy s).rel

/-- 標的関手の単位として、元の comma の円柱の同じ h Fun の射を取る。 -/
def commaSectionUnit {X Y : SSet.{u}} (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X) :
    FunctorHom (𝟙 X) ((s ≫ unitCommaTarget G) ≫ G) :=
  Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (commaSectionUnitHomotopy G s hs))

/-- 構成した単位の各成分は、元の comma の円柱の頂点辺の類と一致する。 -/
lemma commaSectionUnit_component {X Y : SSet.{u}} (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X) (x : X _⦋0⦌) :
    qcatUnitComponent (commaSectionUnit G s hs) x = Truncated.HomotopyCategory.homMk
      (simplicialHomotopyVertexEdge (commaSectionUnitHomotopy G s hs) x).toTruncated :=
  functorHomEvaluate_homotopy (commaSectionUnitHomotopy G s hs) x

end SerrePositivity.InfinityCategories.HomotopyLimits
