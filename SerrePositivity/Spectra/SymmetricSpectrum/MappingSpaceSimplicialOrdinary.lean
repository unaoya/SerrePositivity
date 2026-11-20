module

public import SerrePositivity.CategoryTheory.Enriched.Transport
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpacePointedOrdinary
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceSimplicial
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import SerrePositivity.CategoryTheory.Enriched.Simplicial

/-! # 単体的写像対象と既存のスペクトルの圏構造の一致 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory
open scoped Simplicial

/-- 標準の零次単体のHom同値は、構成済みの零次単体の同値。 -/
lemma mappingSpaceSimplicialCategory_vertexEquiv (E F : SymmetricSpectrum.{u}) :
    let : EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
      pointedMappingEnrichedOrdinaryCategory
    let : SimplicialCategory SymmetricSpectrum.{u} :=
      TransportOrdinaryEnrichment.ordinaryCategory PointedSimplicialSet.forget.{u}
        SymmetricSpectrum.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
        PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}
    SimplicialCategory.homEquiv' E F = simplicialMappingVertexEquiv E F := by
  rfl

end SerrePositivity.SymmetricSpectrum
