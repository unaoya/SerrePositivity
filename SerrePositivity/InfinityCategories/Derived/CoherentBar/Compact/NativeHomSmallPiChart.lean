module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomPiChart
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiChart
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

def dgBarCompactNativeHomSmallPiChart (x y : ClosedCategory R D) (n : ℕ) :=
  (dgBarCompactNativeHomPiChart R D x y n).ofUlift

def dgBarCompactNativeHomSmallPiZeroChart (x y : ClosedCategory R D) :=
  dgBarCompactPiZeroChart_ofUlift (dgBarCompactNativeHomPiZeroChart R D x y)

def dgBarCompactNativeHomSmallEdgeValue {y z : ClosedCategory R D}
    (x : ClosedCategory R D) (f : y ⟶ z) :=
  F2.spaceInfinityEdgeValue ((SSet.Edge.ofTruncated
    (X := (SSet.uliftFunctor.{max u v + 1, max u v}).obj (dgNerve R D))
    (uliftTruncatedEdge.{max u v, max u v + 1}
      ((coherentNerveEdge f).map (coherentComparison (R := R) (D := D))))).map
        (dgBarCompactCoherentUnderlyingValueFunctor R D x))

lemma dgBarCompactNativeHomSmallPiChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j)
    (n : ℕ) (z) (a) :
    (dgBarCompactNativeHomSmallPiChart R D x (F.obj j) n).equiv
      ((dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)).app _ z)
      (dgBarCompactPiMap n (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) z a) =
      HomologicalComplex.homologyMap (dgClosedPostcomposition R D (x := x) (F.map f))
        (-((n + 1 : ℕ) : ℤ))
        ((dgBarCompactNativeHomSmallPiChart R D x (F.obj i) n).equiv z a) :=
  dgBarCompactPiChart_naturality_of_ulift
    (dgBarCompactNativeHomPiChart R D x (F.obj i) n)
    (dgBarCompactNativeHomPiChart R D x (F.obj j) n)
    (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) _
    (dgBarCompactNativeHomPiChart_naturality R D F x f n) z a

lemma dgBarCompactNativeHomSmallPiZeroChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) (a) :
    dgBarCompactNativeHomSmallPiZeroChart R D x (F.obj j)
      (SSet.mapπ₀ (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) a) =
      HomologicalComplex.homologyMap (dgClosedPostcomposition R D (x := x) (F.map f)) 0
        (dgBarCompactNativeHomSmallPiZeroChart R D x (F.obj i) a) :=
  dgBarCompactPiZeroChart_naturality_of_ulift
    (dgBarCompactNativeHomPiZeroChart R D x (F.obj i))
    (dgBarCompactNativeHomPiZeroChart R D x (F.obj j))
    (dgBarCompactNativeHomSmallEdgeValue R D x (F.map f)) _
    (dgBarCompactNativeHomPiZeroChart_naturality R D F x f) a

end SerrePositivity.InfinityCategories
