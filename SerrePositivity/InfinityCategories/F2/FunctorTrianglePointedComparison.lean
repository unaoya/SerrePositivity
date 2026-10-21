module

public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedWitness
public import SerrePositivity.InfinityCategories.F2.ContractibleVertexIsoNaturality

/-!
概要：同じ元の全三角形の実持ち上げと指定持ち上げを、全初期値固定の空間で比較する。
方針：元の全係数を保つ相対延長空間の同じ二頂点を比較する。
規約：各点の比較へ弱めない。使われ方：右辺の全 prism 比較へ写す指定同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s)
local notation "base" => (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram
local notation "v" => snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F

include w in
/-- 元の全初期値と全三角形の底は、元の実証拠から厳密に整合する。 -/
lemma FunctorTrianglePointedWitness.start_projection :
    v ≫ pointedSpaceProjection = (scaffoldFirstVertex 2 ▷ C) ≫ base := by
  rw [← w.start, Category.assoc, w.projection]

/-- 元の全初期値と元の全三角形の底を同時に固定する全選択空間。 -/
def FunctorTrianglePointedWitness.choice :=
  relativeFunctorExtensionSpace pointedSpaceProjection base (scaffoldFirstVertex 2 ▷ C)
    v w.start_projection

/-- 元の全係数を保つ全三角形の選択空間は、全高次を含めて可縮。 -/
lemma FunctorTrianglePointedWitness.choice_contractible : IsContractibleKan w.choice :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection base
    (scaffoldFirstVertex 2 ▷ C) (simplexPrismFirstVertex_leftAnodyne 2 C) v w.start_projection

/-- 同じ元の全底・全初期値の別の実延長を、同じ全選択空間の頂点として保持する。 -/
def FunctorTrianglePointedWitness.point (w' : FunctorTrianglePointedWitness T p s) :
    w.choice _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection base
    (scaffoldFirstVertex 2 ▷ C) v w.start_projection ⟨w'.prism, w'.projection, w'.start⟩

/-- 元の実三角形と元の指定三角形の実持ち上げを、全初期値固定で比較する。 -/
def FunctorTrianglePointedWitness.comparison (hi : s ≫ leftUnstraighteningProjection F = p) :=
  w.choice_contractible.vertexIso (w.point w)
    (w.point (functorTrianglePointedCanonicalWitness T p s hi))

end SerrePositivity.InfinityCategories.F2
