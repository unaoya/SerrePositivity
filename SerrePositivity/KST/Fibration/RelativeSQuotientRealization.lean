module
public import SerrePositivity.KST.Fibration.RelativeSKernelSquare
public import SerrePositivity.KST.SConstruction.CoreAdditivity
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 元の相対 S の商射影と商の core S 実現の厳密な因子化 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の core 包含の後の相対商射影は、同じ完全商関手の core S 写像そのもの。 -/
theorem relativeSimplicialQuotientMap_core {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    relativeSimplicialSConstructionCoreInclusion q.hom ≫ relativeSimplicialQuotientMap q =
      coreSExactMap q := by
  apply NatTrans.ext
  funext n
  exact relativeSQuotientMap_core q n.unop.len

/-- 同じ商の core 実現射を、元の相対 S 実現を通る厳密な因子化として保持する。 -/
theorem relativeSQuotientRealization_core {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q.hom) ≫
        simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q) =
      simplicialDiagonalFunctor.map (coreSExactMap q) := by
  rw [← Functor.map_comp, relativeSimplicialQuotientMap_core]

/-- 各段の元の商比較が局所化で可逆なら、同じ全単体的比較の実現も可逆。
段ごとの比較は Sp 正本の図式局所化から供給する入力であり、ここでは仮定を除去しない。 -/
theorem relativeSQuotientRealization_localized_isIso_of_stages
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))) := by
  apply BisimplicialModel.localized_diagonal_map
  intro n
  exact hq n.unop.len

end SerrePositivity.KST.Fibration
