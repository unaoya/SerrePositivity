module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：元の全 Space 単体と全係数の初点を固定して、構成した pointed 族を比較する。
方針：初点包含の left anodyne 性で同じ相対延長空間の可縮性を使う。
規約：元の全図式・初点・全係数を固定。使われ方：元の普遍三角形への同じ比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex n ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι pointedSpaceProjection
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 同じ全 Space 単体と元の全 Hom の始点を固定した、実 pointed 延長の選択空間。 -/
def spaceSimplexPointedFamilyExtensionSpace : SSet.{u + 1} :=
  relativeFunctorExtensionSpace pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary s)

/-- 同じ全図式と初点を固定する全 pointed 延長の空間は可縮な Kan 複体。 -/
lemma spaceSimplexPointedFamilyExtensionSpace_contractible :
    IsContractibleKan (spaceSimplexPointedFamilyExtensionSpace s) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne n) A)
      v (spaceSimplexPointedFamily_boundary s)

/-- 構成した全 pointed 族を、同じ元の図式と初点の実延長空間の頂点に入れる。 -/
def spaceSimplexPointedFamilyExtensionVertex :
    (spaceSimplexPointedFamilyExtensionSpace s) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary s)
      ⟨spaceSimplexPointedFamily s, spaceSimplexPointedFamily_projection s,
        spaceSimplexPointedFamily_firstVertex s⟩

/-- 元の全図式と同じ初点を保つ任意の持ち上げとの、同じ可縮空間内の指定比較。 -/
def spaceSimplexPointedFamilyComparisonIso
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v) :
    VertexIso (spaceSimplexPointedFamilyExtensionVertex s)
      (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary s) ⟨L, hL, hL₀⟩) :=
  (spaceSimplexPointedFamilyExtensionSpace_contractible s).vertexIso _ _

end SerrePositivity.InfinityCategories.F2
