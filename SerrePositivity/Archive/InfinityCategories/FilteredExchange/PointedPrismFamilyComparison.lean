module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedPrismFamilySection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleIsoComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：可変初期値の同じ二つの全延長を、全パラメータを固定した選択空間で比較する。
方針：全パラメータを定義域に吸収し、同じ底と全境界を固定した相対延長を使う。
規約：各点の比較へ弱めない。使われ方：元の第零面と指定三角形比較の全族の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K : SSet.{u + 1}} {i : C ⟶ A} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) i p)

/-- 全パラメータの元の境界と底を同時に固定した全延長の空間。 -/
def pointedPrismFamilyFixedChoice :=
  relativeFunctorExtensionSpace pointedSpaceProjection (((A ◁ p) ▷ K) ≫ D.diagram)
    ((i ▷ E) ▷ K) D.boundary D.projection

/-- 境界の包含が left anodyne なら、全パラメータを固定した全延長空間も可縮。 -/
lemma pointedPrismFamilyFixedChoice_contractible (hi : leftAnodyneExtensions i) :
    IsContractibleKan (pointedPrismFamilyFixedChoice D) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection _ _
    (leftAnodyneExtensions_whiskerRight _ (leftAnodyneExtensions_whiskerRight i hi E) K) _ _

/-- 元の全延長を、同じ全パラメータの境界と底を固定する空間の実頂点として保持する。 -/
def pointedPrismFamilyFixedChoice_vertex
    (W : (A ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((i ▷ E) ▷ K) ≫ W = D.boundary)
    (hp : W ≫ pointedSpaceProjection = ((A ◁ p) ▷ K) ≫ D.diagram) :
    (pointedPrismFamilyFixedChoice D) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv _ _ _ _ _ ⟨W, hp, hb⟩

/-- 可変初期値を含む全パラメータを固定し、同じ全延長の指定比較を保つ。 -/
def pointedPrismFamilyComparison (hi : leftAnodyneExtensions i)
    (W W' : (A ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((i ▷ E) ▷ K) ≫ W = D.boundary)
    (hp : W ≫ pointedSpaceProjection = ((A ◁ p) ▷ K) ≫ D.diagram)
    (hb' : ((i ▷ E) ▷ K) ≫ W' = D.boundary)
    (hp' : W' ≫ pointedSpaceProjection = ((A ◁ p) ▷ K) ≫ D.diagram) :=
  (pointedPrismFamilyFixedChoice_contractible D hi).vertexIso
    (pointedPrismFamilyFixedChoice_vertex D W hb hp)
    (pointedPrismFamilyFixedChoice_vertex D W' hb' hp')

end SerrePositivity.InfinityCategories.F2
