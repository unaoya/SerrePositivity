module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexVertexCoefficientMaps
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawConstantInterval
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentMorphismPrism
/-!
概要：元の全 pointed 三角形の第一辺を、同じ raw 区間上の実 prism として保持する。
方針：同じ第一面の実初点・中間頂点と、第一 raw 区間の厳密な式を使う。
規約：元の全初期係数・実両端・指定区間を保持する。
使われ方：元の中間比較と第一辺値の貼り合わせ。
-/

@[expose] public section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "g" => coherentColimitApexMiddleCoefficientMap B T
local notation "β" => intervalMappingUncurry
  (SSet.const (coherentColimitRawIntervalVertex B a) : A ⟶ _)
/-- 概要：元の第一面の同じ実 prism。方針：同じ全族を制限する。
規約：全係数を保持。使われ方：第一辺の指定正方形。 -/
def coherentColimitApexPointedFirstPrism : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ spaceSimplexPointedFamily s
/-- 概要：実初点は同じ元の初期係数。方針：元の全族の初点式を使う。
規約：実 fiber を保持。使われ方：固定初点での比較。 -/
lemma coherentColimitApexPointedFirstPrism_start :
    prismEndpoint 0 A ≫ coherentColimitApexPointedFirstPrism B T =
      q ≫ vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone F).vertex := by
  have hi : prismEndpoint 0 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) =
      simplexPrismVertex 2 0 A := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [coherentColimitApexPointedFirstPrism, ← Category.assoc, hi,
    spaceTrianglePointedFamily_source_action]
  exact (coherentColimitApexCoefficientMap_ι B T).symm
/-- 概要：実終点は元の同じ中間係数。方針：同じ全族の中間頂点式を使う。
規約：全係数を保持。使われ方：元の中間比較との照合。 -/
lemma coherentColimitApexPointedFirstPrism_finish :
    prismEndpoint 1 A ≫ coherentColimitApexPointedFirstPrism B T =
      g ≫ vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone G).vertex := by
  have hi : prismEndpoint 1 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) =
      simplexPrismVertex 2 1 A := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [coherentColimitApexPointedFirstPrism, ← Category.assoc, hi]
  exact (coherentColimitApexMiddleCoefficientMap_ι B T).symm
/-- 概要：元の第一面の底は同じ raw 区間の定値族。方針：実第一辺を回収。
規約：区間を変更しない。使われ方：同じ比較の底表示。 -/
lemma coherentColimitApexPointedFirstConstantBase :
    fst (Δ[1] : SSet.{u + 1}) A ≫ SSet.yonedaEquiv.symm (SpaceInfinity.δ 2 s) = β := by
  rw [coherentColimitApexTriangle_first]
  exact (coherentColimitRawConstantInterval_uncurry B a A).symm
/-- 概要：同じ実 prism は元の raw 区間の定値族を被覆する。
方針：元の全射影を制限。規約：実 prism を保持。使われ方：指定比較の底。 -/
lemma coherentColimitApexPointedFirstPrism_projection_constant :
    coherentColimitApexPointedFirstPrism B T ≫ pointedSpaceProjection = β := by
  rw [coherentColimitApexPointedFirstPrism, Category.assoc,
    spaceSimplexPointedFamily_projection, ← Category.assoc, whiskerRight_fst,
    Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact coherentColimitApexPointedFirstConstantBase B T
/-- 概要：元の実第一辺は同じ第一射の元の coherent prism。
方針：同じ正の第一面と実辺の回収を使う。
規約：全係数と実 prism を保持。使われ方：同じ指定対角値の照合。 -/
lemma coherentColimitApexPointedFirstPrism_heq_morphism :
    HEq (coherentColimitApexPointedFirstPrism B T)
      (pointedCoherentMorphismPrism (coherentEdgeHom (SpaceInfinity.δ 2 s))) := by
  have h : coherentColimitApexPointedFirstPrism B T =
      spaceSimplexPointedFamily (SpaceInfinity.δ 2 s) :=
    spaceSimplexPointedFamily_positive_face s (1 : Fin 2)
  exact (heq_of_eq h).trans (spaceEdgePointedFamily_heq_morphism (SpaceInfinity.δ 2 s))
end
end SerrePositivity.InfinityCategories.F2
