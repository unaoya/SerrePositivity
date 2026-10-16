module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SmallDiagramQuotient
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction

/-! # The congruence construction smallifies the large star by a natural quotient

The earlier obstruction ruled out every small natural source. Here all
quotient size and finite-boundary certificates are proved for the opposite
direction, without a model structure in either value universe.
-/

@[expose] public section
universe v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.StarDiagramSmallQuotient
open SmallSubdiagramObstruction

abbrev original : Index (Type v) ⥤ SSet.{v + 1} := diagram (Type v)
abbrev relation : DiagramQuotient.Congruence original.{v} := DiagramQuotient.total original

lemma small (d : Index (Type v)) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient (relation.rel d n)) := by
  exact SmallDiagramQuotient.total_small.{v, v + 1} (F := original) d n

lemma boundary (d : Index (Type v)) :
    SSet.modelCategoryQuillen.I.rlp ((DiagramQuotient.projection relation).app d) := by
  apply SmallDiagramQuotient.total_boundary_rlp original d
  cases d with
  | of d =>
    change (MorphismProperty.monomorphisms SSet.{v + 1}).rlp
      (terminal.from point)
    have := isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ terminalIsTerminal
      (terminal.from point)
    exact (MorphismProperty.monomorphisms _).rlp.of_isIso _
  | star => exact CodiscreteNerveExtension.terminal_mono_rlp PUnit

/-- The actual small strict diagram is the quotient construction, not a chosen constant model. -/
abbrev functor : Index (Type v) ⥤ SSet.{v} :=
  SmallDiagramQuotient.functor.{v, v + 1} relation small

abbrev projection : original.{v} ⟶ functor ⋙ SSet.uliftFunctor.{v + 1, v} :=
  SmallDiagramQuotient.projection.{v, v + 1} relation small

def imageIso {H : Type uH} [Category.{vH} H] (L : SSet.{v + 1} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    original ⋙ L ≅ (functor ⋙ SSet.uliftFunctor.{v + 1, v}) ⋙ L :=
  SmallDiagramQuotient.imageIso.{v, v + 1} relation small boundary L hL

lemma kan (d : Index (Type v)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (functor.obj d)) :=
  SmallDiagramQuotient.kan.{v, v + 1} relation small boundary d
    (values_kan (Type v) PUnit d)

end SerrePositivity.SimplicialModel.StarDiagramSmallQuotient
