module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleSmallTotalAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeModelComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeRepresentationComparison

/-!
概要：元の全三角形の指定比較から、元の二 native 表現間の比較と正方形 hu を構成する。
方針：同じ小全空間比較の単位による像を、元の全 Hom 比較の充満忠実性で反映する。
規約：全三角形・三辺・native 表現・指定比較を保持。使われ方：上側 native 因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "d₀" => coherentTransformationTotalMap F J (coherentVertexOfHomotopy d)
local notation "c₀" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a) ≫
  coherentTransformationTotalMap G J (coherentVertexOfHomotopy b)
local notation "z" => coherentDiagramTotalVertex J
local notation "S" => Iso.inv (smallUnstraighteningHomIso F (KanObject.obj (spaceInfinityObject z)))
local notation "u₀" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F J d₀) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F J d₀))
local notation "u₁" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F J c₀) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F J c₀))

/-- 元の全三角形の指定比較の、同じ単位を保った模型側比較。 -/
def coherentTotalTriangleNativeModelComparison :=
  coherentTotalMapNativeModelComparison F J (functorTriangleSmallTotalActionIso T)

/-- 元の全三角形から、元の長辺と二辺合成の native 表現間へ一意に反映した比較。 -/
def coherentTotalTriangleNativeComparison :=
  coherentTotalMapNativeRepresentationComparison F J d₀ c₀
    (coherentTotalTriangleNativeModelComparison T)

/-- 元の全三角形の指定模型比較は、同じ二 native 表現との正方形 hu を厳密に満たす。 -/
lemma coherentTotalTriangleNativeComparison_square :
    u₀ ≪≫ coherentTotalTriangleNativeModelComparison T =
      VertexIso.map (coherentTotalTriangleNativeComparison T)
        (coherentTotalMapNativeHomComparison F J) ≪≫ u₁ := by
  exact coherentTotalMapNativeRepresentationComparison_square F J d₀ c₀
    (coherentTotalTriangleNativeModelComparison T)

/-- 同じ元の模型比較の像を持つ指定比較は、反映した比較と値まで一致する。 -/
lemma coherentTotalTriangleNativeComparison_unique
    (n : VertexIso (Sigma.fst (coherentTotalMapNativeRepresentation F J d₀))
      (Sigma.fst (coherentTotalMapNativeRepresentation F J c₀)))
    (hn : u₀ ≪≫ coherentTotalTriangleNativeModelComparison T =
      VertexIso.map n (coherentTotalMapNativeHomComparison F J) ≪≫ u₁) :
    n = coherentTotalTriangleNativeComparison T := by
  exact fullyFaithfulComparisonPreimage_unique
    (coherentTotalMapNativeHomComparison_isFullyFaithful F J) u₀ u₁
    (coherentTotalTriangleNativeModelComparison T) n hn

/-- 元の指定比較との値の一致は、同じ模型側の正方形 hu からも、またそのときに限り従う。 -/
lemma coherentTotalTriangleNativeComparison_square_iff
    (n : VertexIso (Sigma.fst (coherentTotalMapNativeRepresentation F J d₀))
      (Sigma.fst (coherentTotalMapNativeRepresentation F J c₀))) :
    (u₀ ≪≫ coherentTotalTriangleNativeModelComparison T =
      VertexIso.map n (coherentTotalMapNativeHomComparison F J) ≪≫ u₁) ↔
      n = coherentTotalTriangleNativeComparison T := by
  constructor
  · exact coherentTotalTriangleNativeComparison_unique T n
  · intro h
    cases h
    exact coherentTotalTriangleNativeComparison_square T

/-- 元の三角形から得た同じ比較は、上側 native 因子の同じ逆と整合する。 -/
lemma coherentTotalTriangleNativeComparison_inverse_naturality :
    coherentTotalTriangleNativeModelComparison T ≪≫
      (coherentTotalMapNativeActionComponentsIso F J c₀).symm =
      (coherentTotalMapNativeActionComponentsIso F J d₀).symm ≪≫
        VertexIso.map (coherentTotalTriangleNativeComparison T)
          (coherentCoconeTransportAction F (coherentDiagramTotalCocone F) z) := by
  exact coherentTotalMapNativeActionComponentsIso_inverse_naturality F J d₀ c₀
    (coherentTotalTriangleNativeComparison T) (coherentTotalTriangleNativeModelComparison T)
    (coherentTotalTriangleNativeComparison_square T)

end SerrePositivity.InfinityCategories.F2
