module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexVertexCoefficientMaps
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawInterval
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawConstantInterval

/-!
概要：明示した元の全 pointed 三角形の最後辺を、元の区間上の実 prism として取り出す。
方針：元の全族の初点・終点作用と、元の余極限三角形の最後辺の厳密な式を使う。
規約：元の最後区間・全係数・実両端を保持。使われ方：元の指定普遍比較の同じ最後辺照合。
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
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexMiddleCoefficientMap B T
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)

/-- 元の同じ全 pointed 族を、元の同じ最後辺へ制限した実 prism。 -/
def coherentColimitApexPointedLastPrism : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ spaceSimplexPointedFamily s

/-- 明示した最後辺 prism の始点は、元の全初点係数の中間像を元の実中間 fiber へ入れた射。 -/
lemma coherentColimitApexPointedLastPrism_start :
    prismEndpoint 0 A ≫ coherentColimitApexPointedLastPrism B T =
      q ≫ vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone G).vertex := by
  have hi : prismEndpoint 0 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      simplexPrismVertex 2 1 A := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [coherentColimitApexPointedLastPrism, ← Category.assoc, hi]
  exact (coherentColimitApexMiddleCoefficientMap_ι B T).symm

/-- 明示した最後辺 prism の終点は、元の実終 fiber 内の同じ全係数作用。 -/
lemma coherentColimitApexPointedLastPrism_finish :
    prismEndpoint 1 A ≫ coherentColimitApexPointedLastPrism B T =
      g ≫ vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone J).vertex := by
  have hi : prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      simplexPrismVertex 2 2 A := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [coherentColimitApexPointedLastPrism, ← Category.assoc, hi]
  exact (coherentColimitApexTargetCoefficientMap_ι B T).symm

/-- 明示した同じ最後辺 prism は、元の同じ指定最後区間を全係数で厳密に被覆する。 -/
lemma coherentColimitApexPointedLastPrism_projection :
    coherentColimitApexPointedLastPrism B T ≫ pointedSpaceProjection =
      (Δ[1] ◁ (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : A ⟶ Δ[0])) ≫
        intervalMappingUncurry D := by
  rw [coherentColimitApexPointedLastPrism, Category.assoc, spaceSimplexPointedFamily_projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm, coherentColimitApexTriangle_last,
    coherentColimitRawIntervalVertex_uncurry, ← Category.assoc, whiskerLeft_fst]

/-- 最後辺の実 prism の底は、元の指定区間頂点の全係数上の定値族そのもの。 -/
lemma coherentColimitApexPointedLastPrism_projection_constant :
    coherentColimitApexPointedLastPrism B T ≫ pointedSpaceProjection =
      intervalMappingUncurry (SSet.const (coherentColimitRawIntervalVertex B b) : A ⟶ _) := by
  rw [coherentColimitApexPointedLastPrism, Category.assoc,
    spaceSimplexPointedFamily_projection, ← Category.assoc, whiskerRight_fst,
    Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm, coherentColimitApexTriangle_last]
  exact (coherentColimitRawConstantInterval_uncurry B b A).symm

end SerrePositivity.InfinityCategories.F2
