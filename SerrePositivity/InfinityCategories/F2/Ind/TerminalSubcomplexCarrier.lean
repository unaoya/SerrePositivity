module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalSubcomplexRealization
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：小さい終頂点付き部分複体の同じ実現空間と二つの射影。
方針：既存の実現空間を特殊化し、包含順の nerve への trivial Kan 射影を再利用する。
規約：元の単体集合の quasicategory 性を実現空間の仮定にしない。
使われ方：coslice の有限余錐を作って値写像の cofinal 性を検出する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) (X : SSet.{u})

/-- 同じ部分複体の全鎖を実現する空間。 -/
abbrev terminalSubcomplexCarrier : SSet.{u} :=
  (terminalCarrier (fun A : SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X) => A.val)
    (fun A => (terminalSubcomplexChosenVertex κ X A).val)).toSSet

/-- 元の単体集合への同じ値写像。 -/
def terminalSubcomplexCarrierValue : terminalSubcomplexCarrier κ X ⟶ X :=
  terminalCarrierValue _ _

/-- 元の包含順への同じ射影。 -/
def terminalSubcomplexCarrierProjection : terminalSubcomplexCarrier κ X ⟶
    nerve (SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X)) :=
  terminalCarrierProjection _ _

instance terminalSubcomplexCarrierProjection_trivialKanFibration :
    TrivialKanFibration (terminalSubcomplexCarrierProjection κ X) :=
  terminalCarrierProjection_trivialKanFibration
    (fun A : SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X) => A.val) (fun _ _ h => h)
    (terminalSubcomplexChosenVertex κ X) (terminalSubcomplexChosenVertex_terminal κ X)

instance terminalSubcomplexCarrier_quasicategory : Quasicategory (terminalSubcomplexCarrier κ X) :=
  quasicategory_of_innerFibration (terminalSubcomplexCarrierProjection κ X)

end SerrePositivity.InfinityCategories.F2.Ind
