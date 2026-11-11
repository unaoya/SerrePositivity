module
public import SerrePositivity.KST.Fibration.RelativeSKernelDiagonalContraction
public import SerrePositivity.KST.Fibration.WeakStringRelativeMultiRealization

/-! # 元の Verdier 包含側の W 列の単回実現の対角の可縮性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ相対 S との比較により、包含側の元の W 列対角の一点射は局所化同型。 -/
theorem weakStringKernelDiagonal_toPoint_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from
      (simplicialDiagonalFunctor.obj (weakStringMultiRealization (i ≫ q : A ⟶ C) 1)))) := by
  have hc := relativeSWeakStringMultiComparison_localized_isIso (i ≫ q : A ⟶ C)
  have he : relativeSWeakStringMultiComparison (i ≫ q : A ⟶ C) ≫ terminal.from
      (simplicialDiagonalFunctor.obj (weakStringMultiRealization (i ≫ q : A ⟶ C) 1)) =
        terminal.from (simplicialDiagonalFunctor.obj
          (relativeSimplicialSConstruction (i.hom ≫ q.hom))) := terminal.hom_ext _ _
  have hs := relativeSKernelDiagonal_toPoint_localized_isIso h
  rw [← he, Functor.map_comp] at hs
  exact (isIso_comp_left_iff _ _).mp hs

end SerrePositivity.KST.Fibration
