module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpacePointedOrdinary
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceSimplicialEnriched
public import SerrePositivity.CategoryTheory.Enriched.Transport
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

/-- 基点を忘れた写像対象による、既存の圏構造と整合する単体的豊穣構造。 -/
@[instance_reducible]
def mappingSpaceSimplicialCategory : SimplicialCategory SymmetricSpectrum.{u} := by
  let : EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
    pointedMappingEnrichedOrdinaryCategory
  exact TransportOrdinaryEnrichment.ordinaryCategory PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}

/-- 単体的豊穣構造の写像対象は、基点を忘れた既存の写像対象。 -/
lemma mappingSpaceSimplicialCategory_hom (E F : SymmetricSpectrum.{u}) :
    mappingSpaceSimplicialCategory.Hom E F = simplicialMappingSpace E F := rfl

/-- 標準の零次単体のHom同値は、構成済みの零次単体の同値。 -/
lemma mappingSpaceSimplicialCategory_vertexEquiv (E F : SymmetricSpectrum.{u}) :
    let : SimplicialCategory SymmetricSpectrum.{u} := mappingSpaceSimplicialCategory
    SimplicialCategory.homEquiv' E F = simplicialMappingVertexEquiv E F := by
  rfl

/-- 通常の圏構造と接続した豊穣構造の基礎データは構成済みの豊穣構造。 -/
lemma mappingSpaceSimplicialCategory_enriched :
    mappingSpaceSimplicialCategory.toEnrichedCategory = simplicialMappingEnrichedCategory := rfl

/-- 零次単体への同値が恒等射を単体的な単位へ送るという法則。 -/
def simplicialMappingVertexIdentityLaw (E : SymmetricSpectrum.{u}) : Prop :=
  let : SimplicialCategory SymmetricSpectrum.{u} := mappingSpaceSimplicialCategory
  SimplicialHomLaws.identityLaw E

/-- 零次単体への同値は恒等射を保つ。 -/
lemma simplicialMappingVertex_identity (E : SymmetricSpectrum.{u}) :
    simplicialMappingVertexIdentityLaw E := by
  let : SimplicialCategory SymmetricSpectrum.{u} := mappingSpaceSimplicialCategory
  exact SimplicialHomLaws.identity E

/-- 零次単体への同値が通常の合成を単体的な合成へ送るという法則。 -/
def simplicialMappingVertexCompositionLaw {E F G : SymmetricSpectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  let : SimplicialCategory SymmetricSpectrum.{u} := mappingSpaceSimplicialCategory
  SimplicialHomLaws.compositionLaw f g

/-- 零次単体への同値は通常のスペクトル射の合成を保つ。 -/
lemma simplicialMappingVertex_composition {E F G : SymmetricSpectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) : simplicialMappingVertexCompositionLaw f g := by
  let : SimplicialCategory SymmetricSpectrum.{u} := mappingSpaceSimplicialCategory
  exact SimplicialHomLaws.composition f g

end SerrePositivity.SymmetricSpectrum
