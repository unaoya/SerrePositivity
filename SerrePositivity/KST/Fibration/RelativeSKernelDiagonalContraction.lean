module
public import SerrePositivity.KST.Fibration.RelativeSKernelContraction
public import SerrePositivity.KST.Fibration.WeakStringRealizationConstants
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 元の核の相対 S の対角から一点への実射の可逆性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 各行の実際の一点への射を、全単体作用素とともに保持する。 -/
def simplicialSpaceToPoint (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    F ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (⊤_ SSet.{u}) where
  app n := terminal.from (F.obj n)
  naturality {_ _} _ := terminal.hom_ext _ _

/-- 元の核の各相対 S の収縮から、元の対角の同じ一点射も局所化同型。 -/
theorem relativeSKernelDiagonal_toPoint_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from
      (simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction (i.hom ≫ q.hom))))) := by
  let F := relativeSimplicialSConstruction (i.hom ≫ q.hom)
  let c := simplicialSpaceToPoint F
  have hd : IsIso (AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map c)) := by
    apply BisimplicialModel.localized_diagonal_map
    intro n
    exact relativeSKernel_toPoint_localized_isIso h n.unop.len
  have he : simplicialDiagonalFunctor.map c ≫ (constantSSetDiagonalIso (⊤_ SSet.{u})).hom =
      terminal.from (simplicialDiagonalFunctor.obj F) := terminal.hom_ext _ _
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (terminal.from (simplicialDiagonalFunctor.obj F)))
  rw [← he, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
