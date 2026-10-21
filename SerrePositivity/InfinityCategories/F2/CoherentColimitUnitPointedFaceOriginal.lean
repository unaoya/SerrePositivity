module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFaceIso
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedChoice
public import SerrePositivity.InfinityCategories.F2.TriangleLongPrismRestriction

/-!
概要：固定始点を持つ元の二面と、元の指定三角形の実持ち上げを比較する。
方針：同じ全初期値の選択空間へ元の二頂点を入れ、長辺へ制限する。
規約：同じ全空間と同じ始点を保持。使われ方：共有面の指定比較を同じ空間で消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "h₀" => coherentColimitUnitPointedFace_initial B T k j hj S.diagram hS
local notation "m" => coherentColimitUnitPointedFaceMap B T k j hj S.diagram hS
local notation "hc" => leftUnstraighteningSimplexChoiceSpace_isContractibleKan F 2
  (functorSimplexDiagram S.diagram) h₀
local notation "v" => functorTrianglePointedChoiceVertex S h₀
local notation "pr" => leftUnstraighteningSimplexStart_projection F 2
  (functorSimplexDiagram S.diagram) h₀
local notation "R" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  ((Δ[2] ◁ leftUnstraighteningProjection F) ≫ functorSimplexDiagram S.diagram)
  (leftUnstraighteningSimplexStart F) pr

/-- 各元の全三単体の実二面を、元の指定三角形の同じ実持ち上げと比較する。 -/
def coherentColimitUnitPointedFaceOriginalComparison
    (x : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌) :=
  (hc).vertexIso ((m).app (Opposite.op ⦋0⦌) x) v

/-- 元の実二面と指定三角形の比較を、同じ全始点を持つ長辺へ制限する。 -/
def coherentColimitUnitPointedFaceOriginalLongComparison
    (x : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌) :=
  VertexIso.map (coherentColimitUnitPointedFaceOriginalComparison B T k j hj S hS x) R

/-- 制限した指定比較は、同じ二つの実長辺の可縮空間の指定比較そのもの。 -/
lemma coherentColimitUnitPointedFaceOriginalLongComparison_eq
    (x : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌) :
    coherentColimitUnitPointedFaceOriginalLongComparison B T k j hj S hS x =
      (triangleLongPrismExtension_contractible pointedSpaceProjection
        ((Δ[2] ◁ leftUnstraighteningProjection F) ≫ functorSimplexDiagram S.diagram)
        (leftUnstraighteningSimplexStart F) pr).vertexIso
        ((R).app (Opposite.op ⦋0⦌) ((m).app (Opposite.op ⦋0⦌) x))
        ((R).app (Opposite.op ⦋0⦌) v) :=
  triangleLongPrismExtensionRestriction_vertexIso _ _ _ _
    (coherentColimitUnitPointedFaceOriginalComparison B T k j hj S hS x)

end SerrePositivity.InfinityCategories.F2
