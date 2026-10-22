module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionEvaluation
public import SerrePositivity.InfinityCategories.Stable.SuspensionFiniteColimits
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：同じ源の全単体族を比較し実格子と選択した suspension 関手を全関手同型にする。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def ExcisionSquareGrid.suspension_family_comparison {X : SSet.{u}} [Quasicategory X]
    [TrivialKanFibration (suspensionDiagramEvaluation X 0 0)]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) (hR : IsPushoutSquare R) (s : X ⟶ suspensionDiagrams X)
    (hs : s ≫ suspensionDiagramEvaluation X 0 0 = 𝟙 X) :
    FunctorIso (d.suspension_family hz hR) (R ≫ s) :=
  functorIsoOfTrivialKanFibration (suspensionDiagramEvaluation X 0 0)
    (d.suspension_family hz hR) (R ≫ s) (by
      rw [d.suspension_family_source hz hR, Category.assoc, hs, Category.comp_id])

def ExcisionSquareGrid.suspension_target_comparison {X : SSet.{u}} [Quasicategory X]
    [TrivialKanFibration (suspensionDiagramEvaluation X 0 0)]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) (hR : IsPushoutSquare R) (s : X ⟶ suspensionDiagrams X)
    (hs : s ≫ suspensionDiagramEvaluation X 0 0 = 𝟙 X) :
    FunctorIso ((β_ Δ[1] Δ[1]).hom ≫ excisionGridFinalSquare ≫ d.extension.full)
      (R ≫ s ≫ suspensionDiagramEvaluation X 1 1) := by
  let e := FunctorIso.postcomp (d.suspension_family_comparison hz hR s hs)
    (suspensionDiagramEvaluation X 1 1)
  simpa only [d.suspension_family_target hz hR, Category.assoc] using e

def ExcisionSquareGrid.suspension_functor_comparison {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteColimits X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) (hR : IsPushoutSquare R) :
    FunctorIso ((β_ Δ[1] Δ[1]).hom ≫ excisionGridFinalSquare ≫ d.extension.full)
      (R ≫ suspensionFunctorOfFiniteColimits X) := by
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits X
  exact d.suspension_target_comparison hz hR (suspensionDiagramSectionOfFiniteColimits X)
    (suspensionDiagramSectionOfFiniteColimits_source X)

end SerrePositivity.InfinityCategories
