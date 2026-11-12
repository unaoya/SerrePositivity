module
public import SerrePositivity.KST.Fibration.WeakStringRelativeDiagonal
public import SerrePositivity.KST.SConstruction.CoreAdditivity
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 元の相対 S の対角と W 列の core S 実現の対角との実比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 各 W 列の元の object/core 比較を、全ての列方向の作用とともに束ねる。 -/
def weakStringObjectCoreComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringStableSimplicial q ⋙ objectSConstructionFunctor ⟶
      weakStringStableSimplicial q ⋙ coreSRealizationFunctor :=
  Functor.whiskerLeft (weakStringStableSimplicial q) objectCoreRealizationComparison

/-- 各行の K-1 object/core 比較から、元の実二重単体写像の対角が局所化同型になる。 -/
theorem weakStringObjectCoreComparison_diagonal_localized_isIso
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (weakStringObjectCoreComparison q))) := by
  apply BisimplicialModel.localized_diagonal_map
  intro n
  exact objectToCoreSRealization_localized_isIso (weakStringCategory q n.unop)

/-- 元の相対 S の対角から W 列の core S 実現の対角への、全高次単体を保つ実際の射。 -/
def relativeSWeakStringCoreComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction q.hom) ⟶
      simplicialDiagonalFunctor.obj (weakStringStableSimplicial q ⋙ coreSRealizationFunctor) :=
  (weakStringObjectRelativeDiagonalIso q).inv ≫
    simplicialDiagonalFunctor.map (weakStringObjectCoreComparison q)

/-- 同じ相対 S と W 列の core S 実現の比較そのものは、anodyne 局所化で同型。 -/
theorem relativeSWeakStringCoreComparison_localized_isIso
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeSWeakStringCoreComparison q)) := by
  have := weakStringObjectCoreComparison_diagonal_localized_isIso q
  unfold relativeSWeakStringCoreComparison
  rw [Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
