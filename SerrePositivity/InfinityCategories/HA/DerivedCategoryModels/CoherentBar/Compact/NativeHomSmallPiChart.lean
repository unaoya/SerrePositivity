module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomPiChart
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiChart
/-!
概要：native Hom 値のチャートから比較用の追加宇宙を取り除く。
方針：元の全基点 π・π₀ の持ち上げ同型で前合成する。
規約：元の対象宇宙と同じ実辺作用を維持する。
使われ方：実加群評価空間のホモロジーチャートと五条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

def dgBarCompactNativeHomSmallPiChart (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) (n : ℕ) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiChart R D x y n).ofUlift

def dgBarCompactNativeHomSmallPiZeroChart (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_ofUlift (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiZeroChart R D x y)

def dgBarCompactNativeHomSmallEdgeValue {y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D}
    (x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) (f : y ⟶ z) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue ((SSet.Edge.ofTruncated
    (X := (SSet.uliftFunctor.{max u v + 1, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max u v, max u v + 1}
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))))).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor R D x))

lemma dgBarCompactNativeHomSmallPiChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j)
    (n : ℕ) (z) (a) :
    (dgBarCompactNativeHomSmallPiChart R D x (F.obj j) n).equiv
      ((dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) z a) =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) (F.map f))
        (-((n + 1 : ℕ) : ℤ))
        ((dgBarCompactNativeHomSmallPiChart R D x (F.obj i) n).equiv z a) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiChart_naturality_of_ulift
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiChart R D x (F.obj i) n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiChart R D x (F.obj j) n)
    (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiChart_naturality R D F x f n) z a

lemma dgBarCompactNativeHomSmallPiZeroChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) (a) :
    dgBarCompactNativeHomSmallPiZeroChart R D x (F.obj j)
      (SSet.mapπ₀ (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) a) =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) (F.map f)) 0
        (dgBarCompactNativeHomSmallPiZeroChart R D x (F.obj i) a) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_naturality_of_ulift
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiZeroChart R D x (F.obj i))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiZeroChart R D x (F.obj j))
    (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomPiZeroChart_naturality R D F x f) a

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
