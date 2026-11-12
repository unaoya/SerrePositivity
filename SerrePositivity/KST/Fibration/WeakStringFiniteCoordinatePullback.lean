module
public import SerrePositivity.KST.Fibration.WeakStringFinitePostMap
public import SerrePositivity.KST.Fibration.WeakStringFiniteKernelIso
public import SerrePositivity.KST.Fibration.ProductCoefficientHomotopyPullback

/-! # 元の有限比較の積座標上の初期成分のホモトピー引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の有限比較の積座標の後合成と、元の初期成分への射影の可換四角形。 -/
theorem weakStringFiniteInitialPostSquare {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    CommSq (fst _ _) (weakStringFinitePostMap f q n r)
      ((multiRealizationFunctor r).map (topPostExact f)) (fst _ _) :=
  ⟨(weakStringFinitePostMap_initial f q n r).symm⟩

/-- Verdier 列では、同じ有限積座標上の初期成分の実四角形は全長・全正反復で homotopy pullback。 -/
theorem weakStringFiniteInitialPostSquare_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n r : ℕ) :
    IsHomotopyPullback (weakStringFiniteInitialPostSquare i q n (r + 1)) :=
  productCoefficientSquare_homotopyPullback _ _
    (weakStringFiniteKernelPostMap_verdier_localized_isIso h n r)

end SerrePositivity.KST.Fibration
