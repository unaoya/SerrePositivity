module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexVertexCoefficientMaps
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawInterval

/-!
概要：明示した元の全 pointed 三角形の長辺を、元の区間上の実 prism として取り出す。
方針：元の全族の初点・終点作用と、元の余極限三角形の長辺の厳密な式を使う。
規約：元の長区間・全係数・実両端を保持。使われ方：元の指定普遍比較の同じ長辺照合。
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
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)

/-- 元の同じ全 pointed 族を、元の同じ長辺へ制限した実 prism。 -/
def coherentColimitApexPointedLongPrism : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ spaceSimplexPointedFamily s

/-- 明示した長辺 prism の始点は、元の全初点係数を元の実初点 fiber へ入れた射。 -/
lemma coherentColimitApexPointedLongPrism_start :
    prismEndpoint 0 A ≫ coherentColimitApexPointedLongPrism B T =
      q ≫ vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone F).vertex := by
  have hi : prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      simplexPrismVertex 2 0 A := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [coherentColimitApexPointedLongPrism, ← Category.assoc, hi,
    spaceTrianglePointedFamily_source_action]
  exact (coherentColimitApexCoefficientMap_ι B T).symm

/-- 明示した長辺 prism の終点は、元の実終 fiber 内の同じ全係数作用。 -/
lemma coherentColimitApexPointedLongPrism_finish :
    prismEndpoint 1 A ≫ coherentColimitApexPointedLongPrism B T =
      g ≫ vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone J).vertex := by
  have hi : prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      simplexPrismVertex 2 2 A := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [coherentColimitApexPointedLongPrism, ← Category.assoc, hi]
  exact (coherentColimitApexTargetCoefficientMap_ι B T).symm

/-- 明示した同じ長辺 prism は、元の同じ指定長区間を全係数で厳密に被覆する。 -/
lemma coherentColimitApexPointedLongPrism_projection :
    coherentColimitApexPointedLongPrism B T ≫ pointedSpaceProjection =
      (Δ[1] ◁ (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : A ⟶ Δ[0])) ≫
        intervalMappingUncurry D := by
  rw [coherentColimitApexPointedLongPrism, Category.assoc, spaceSimplexPointedFamily_projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm, coherentColimitApexTriangle_long,
    coherentColimitRawIntervalVertex_uncurry, ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories.F2
