module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity

/-!
概要：構成した像拡大の実射を、k-connective 不変量の元の Perf の値の射へ渡す。
方針：実代数の連結度と π₀ 同型を、既存の IsKConnective 条件へ適用する。
規約：値の射は既存の Perf extension。使われ方：LT のレベル表示から値の塔への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})
  {B C : Mon (Complex R)} [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma IsKConnective.postnikovImageProjection_connected {k : ℤ} (h : IsKConnective R Φ k) :
    (∀ j : ℤ, j < n + 1 + k →
      Function.Injective (invariantGroupMap R Φ (postnikovImageProjection R f n hn) j)) ∧
    ∀ j : ℤ, j ≤ n + 1 + k →
      Function.Surjective (invariantGroupMap R Φ (postnikovImageProjection R f n hn) j) :=
  h.2 (postnikovImageExtension_isConnective R f n hn) (postnikov_isConnective R B n)
    (postnikovImageProjection R f n hn) (n + 1) (by omega)
    (postnikovImageProjection_groups_bijective R f n hn 0 hn)
    (DGAlgebra.postnikovImageProjection_connected R f n hn)

lemma IsKConnective.postnikovSourceImageFactor_connected {k : ℤ} (h : IsKConnective R Φ k)
    (hn' : 1 ≤ n) :
    (∀ j : ℤ, j < n + k →
      Function.Injective (invariantGroupMap R Φ (postnikovSourceImageFactor R f n hn) j)) ∧
    ∀ j : ℤ, j ≤ n + k →
      Function.Surjective (invariantGroupMap R Φ (postnikovSourceImageFactor R f n hn) j) :=
  h.2 (postnikov_isConnective R B (n + 1)) (postnikovSourceImageExtension_isConnective R f n hn)
    (postnikovSourceImageFactor R f n hn) n hn'
    (postnikovSourceImageFactor_groups_bijective R f n hn 0 hn)
    (DGAlgebra.postnikovSourceImageFactor_connected R f n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
