module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionTetrahedronZeroCylinder
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionTetrahedronZeroFamily
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyEndpointEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyTensorRight
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：零面の実 coslice 円柱を元の全反転 Hom 係数の pointed 族へ移す。
方針：係数を恒等に固定し、元の coslice 前合成と標準正規化を後合成する。
規約：同じ実円柱と全係数を保持する。
使われ方：始点固定延長空間の指定比較との一致を証明する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "T" => coherentCompositionTetrahedron s
local notation "M" => coherentSimplexMaximalization s
local notation "Z" => sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K))
local notation "g" => SSet.yonedaEquiv.symm
  (SimplicialObject.δ Z 0 (spaceSimplexSourceCone T))
local notation "E" => coherentCosliceSourcePrecomposition pointKanObject K ≫
  pointedCoherentCosliceIso.hom

/-- 零面の全 pointed 族は元の実 coslice 零面を同じ全係数で前合成した族。 -/
lemma spaceCompositionZeroFamily_eq_coslice :
    spaceCompositionTetrahedronZeroFamily s = (g ▷ A) ≫ E := by
  have hc : stdSimplex.δ (0 : Fin 4) ≫ SSet.yonedaEquiv.symm (spaceSimplexSourceCone T) =
      g := SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ (0 : Fin 4)) _
  have hw := congrArg (fun f ↦ (f ▷ A) ≫ E) hc
  rw [comp_whiskerRight, Category.assoc] at hw
  exact hw

/-- 標準族は同じ全係数前合成と元の正規化の合成そのもの。 -/
lemma spaceCompositionStandardFamily_eq_coslice :
    spaceSimplexPointedFamily M =
      (SSet.yonedaEquiv.symm (spaceSimplexSourceCone M) ▷ A) ≫ E := rfl

/-- 元の coslice 円柱を同じ全係数で移した実ホモトピー。 -/
def spaceCompositionZeroPointedRawHomotopy :=
  functorHomotopyPostcomp
    (functorHomotopyTensorRight (spaceCompositionTetrahedronZeroCosliceHomotopy s) A) E

/-- 元の標準族から零面の実族への、全独立 Hom 係数を保持した実ホモトピー。 -/
def spaceCompositionZeroPointedHomotopy :
    SSet.Homotopy (spaceSimplexPointedFamily M) (spaceCompositionTetrahedronZeroFamily s) :=
  functorHomotopyOfEndpointEq (spaceCompositionZeroPointedRawHomotopy s)
    (spaceCompositionStandardFamily_eq_coslice s).symm
    (spaceCompositionZeroFamily_eq_coslice s).symm

/-- 両端を元の族へ揃えても全係数の実円柱は同じ射。 -/
lemma spaceCompositionZeroPointedHomotopy_h :
    (spaceCompositionZeroPointedHomotopy s).h =
      (spaceCompositionZeroPointedRawHomotopy s).h :=
  functorHomotopyOfEndpointEq_h (spaceCompositionZeroPointedRawHomotopy s)
    (spaceCompositionStandardFamily_eq_coslice s).symm
    (spaceCompositionZeroFamily_eq_coslice s).symm

end SerrePositivity.InfinityCategories.F2
