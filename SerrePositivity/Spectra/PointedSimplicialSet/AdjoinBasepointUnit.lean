module

public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepoint

/-! # 零次標準単体への基点追加とsmashの単位の比較 -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Simplicial

/-- 零次標準単体と終単体的集合の同型。 -/
def deltaZeroUnitIso : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit

/-- 零次標準単体への自由な基点追加はsmashの単位と同型。 -/
def adjoinBasepointDeltaZeroIso :
    adjoinBasepoint (Δ[0] : SSet.{u}) ≅ 𝟙_ PointedSimplicialSet.{u} :=
  adjoinBasepointFunctor.mapIso deltaZeroUnitIso ≪≫ adjoinBasepointUnitIso

end SerrePositivity.PointedSimplicialSet
