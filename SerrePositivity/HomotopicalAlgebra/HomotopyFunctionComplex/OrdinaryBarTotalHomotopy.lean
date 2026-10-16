module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation
public import SerrePositivity.CategoryTheory.NerveHomotopyUniverse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # Actual nerve homotopy of the whole labelled total comparison

The source is the nerve of the original bar simplex category. The target
retains comma objects, degrees, and Hom labels. This is an auxiliary
homotopy; no comparison between this nerve and the original bar is assumed.
-/

@[expose] public section
universe v u uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev firstMap := NerveHomotopyUniverse.map (OrdinaryBarTotalCone.first R)
abbrev evaluatedMap := NerveHomotopyUniverse.map
  (OrdinaryBarTotalEvaluation.evaluationElements R a b ⋙
    OrdinaryBarTotalEvaluation.rowElements R)

def homotopy : SSet.Homotopy (firstMap R) (evaluatedMap R a b) :=
  NerveHomotopyUniverse.homotopy (OrdinaryBarTotalEvaluation.comparison R a b)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma image_eq : L.map (firstMap R) = L.map (evaluatedMap R a b) :=
  AnodyneHomotopy.map_homotopy_eq L hL (homotopy R a b)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy
