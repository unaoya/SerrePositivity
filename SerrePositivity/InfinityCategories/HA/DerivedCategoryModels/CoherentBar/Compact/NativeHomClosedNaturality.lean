module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomSmallPiChart
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
/-!
概要：任意の単独の閉射に沿う native Hom チャートの自然性。
方針：同じ閉射を小さい平行対図式の一辺として用いる。
規約：元の coherent 図式全体を ordinary 図式へ置き換えない。
使われ方：bar の実 transition と余錐の脚をそれぞれ評価する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

lemma dgBarCompactNativeHomSmallPiChart_closedNaturality
    {y y' : ClosedCategory R D} (x : ClosedCategory R D) (f : y ⟶ y')
    (n : ℕ) (z) (a) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart R D x y' n).equiv
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallEdgeValue R D x f).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallEdgeValue R D x f) z a) =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) f)
        (-((n + 1 : ℕ) : ℤ)) ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart R D x y n).equiv z a) := by
  let F : AsSmall.{u} WalkingParallelPair ⥤ ClosedCategory R D :=
    AsSmall.down ⋙ parallelPair f f
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart_naturality R D F x
    ((AsSmall.up (C := WalkingParallelPair)).map WalkingParallelPairHom.left) n z a

lemma dgBarCompactNativeHomSmallPiZeroChart_closedNaturality
    {y y' : ClosedCategory R D} (x : ClosedCategory R D) (f : y ⟶ y') (a) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiZeroChart R D x y'
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallEdgeValue R D x f) a) =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) f) 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiZeroChart R D x y a) := by
  let F : AsSmall.{u} WalkingParallelPair ⥤ ClosedCategory R D :=
    AsSmall.down ⋙ parallelPair f f
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiZeroChart_naturality R D F x
    ((AsSmall.up (C := WalkingParallelPair)).map WalkingParallelPairHom.left) a

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
