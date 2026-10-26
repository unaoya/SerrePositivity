module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiChartEquivalence
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.StandardClosedPostcomposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.LinearUnderlyingValueComparison
/-!
概要：元の dg nerve の native Hom 値へ全基点チャートを渡す。
方針：線形 Hom の全空間比較の実逆データを固定する。
規約：同じ native 値と実辺を使い、coherent 図式を strict 化しない。
使われ方：元の評価ホモロジー余錐を native 空間の五条件へ接続する。
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

/-- 線形模型の道に不変な全基点チャート。 -/
def dgBarCompactLinearHomPiChart (x y : D) (n : ℕ) :=
  dgBarCompactModuleZeroPiChart (dgBarCompactLinearHomModule (R := R) x y) n
    (dgBarCompactLinearHomZeroBaseCohomologyEquiv x y n).toEquiv

/-- 同じ全空間比較から選んだ実逆データ。 -/
def dgBarCompactLinearNativeHomEquivalence (x y : ClosedCategory R D) :
    QCatEquivalence (moduleUnderlyingSSet (dgBarCompactLinearHomModule (R := R) x y))
      ((SSet.uliftFunctor.{max u v + 1, max u v}).obj
        (spaceInfinityObject ((dgBarCompactCoherentUnderlyingValueFunctor R D x).app
          (Opposite.op ⦋0⦌) (ULift.up
            ((coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌)
              (coherentNerveVertex y))))).obj) :=
  (dgBarCompactLinearUnderlyingValueComparison_isQCatEquivalence R D x y).choose

/-- native Hom 値の追加宇宙での全基点チャート。 -/
def dgBarCompactNativeHomPiChart (x y : ClosedCategory R D) (n : ℕ) :=
  (dgBarCompactLinearHomPiChart R D x y n).ofEquivalence
    (dgBarCompactLinearNativeHomEquivalence R D x y)

/-- 元の coherent 辺による native 値の実作用。 -/
def dgBarCompactNativeHomEdgeValue {y z : ClosedCategory R D} (x : ClosedCategory R D)
    (f : y ⟶ z) :=
  (SSet.uliftFunctor.{max u v + 1, max u v}).map
    (F2.spaceInfinityEdgeValue ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max u v + 1, max u v}).obj (dgNerve R D))
      (uliftTruncatedEdge.{max u v, max u v + 1}
        ((coherentNerveEdge f).map (coherentComparison (R := R) (D := D))))).map
          (dgBarCompactCoherentUnderlyingValueFunctor R D x)))

lemma dgBarCompactNativeHomPiChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j)
    (n : ℕ) (z) (a) :
    (dgBarCompactNativeHomPiChart R D x (F.obj j) n).equiv
      ((dgBarCompactNativeHomEdgeValue R D x (F.map f)).app _ z)
      (dgBarCompactPiMap n (dgBarCompactNativeHomEdgeValue R D x (F.map f)) z a) =
      HomologicalComplex.homologyMap (dgClosedPostcomposition R D (x := x) (F.map f))
        (-((n + 1 : ℕ) : ℤ)) ((dgBarCompactNativeHomPiChart R D x (F.obj i) n).equiv z a) := by
  let φ := dgClosedPostcomposition R D (x := x) (F.map f)
  have h := dgBarCompactLinearUnderlyingValueComparison_transportIso R D F x f
  have hs : (HomotopyLimits.simplicialHomDiagram F x).map f =
      moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap φ) :=
    dgBarCompactStandardSimplicialPostcomp_chainMap R D (F.map f)
  rw [show ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) =
    SSet.opFunctor.map (moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap φ)) from
      congrArg SSet.opFunctor.map hs] at h
  exact dgBarCompactPiChart_naturality_of_comparison
    (dgBarCompactLinearHomPiChart R D x (F.obj i) n)
    (dgBarCompactLinearHomPiChart R D x (F.obj j) n)
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj i))
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj j))
    (moduleUnderlyingSSetMap (dgBarCompactLinearHomCohomologyMap φ))
    (dgBarCompactNativeHomEdgeValue R D x (F.map f)) _ h
    (dgBarCompactLinearHomPiCohomologyEquiv_naturality φ n) z a

/-- 同じ実比較を使う native Hom 値の零次数チャート。 -/
def dgBarCompactNativeHomPiZeroChart (x y : ClosedCategory R D) :=
  dgBarCompactPiZeroChart_ofEquivalence
    (dgBarCompactLinearHomPiZeroCohomologyEquiv x y)
    (dgBarCompactLinearNativeHomEquivalence R D x y)

lemma dgBarCompactNativeHomPiZeroChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) (a) :
    dgBarCompactNativeHomPiZeroChart R D x (F.obj j)
      (SSet.mapπ₀ (dgBarCompactNativeHomEdgeValue R D x (F.map f)) a) =
      HomologicalComplex.homologyMap (dgClosedPostcomposition R D (x := x) (F.map f)) 0
        (dgBarCompactNativeHomPiZeroChart R D x (F.obj i) a) := by
  let φ := dgClosedPostcomposition R D (x := x) (F.map f)
  have h := dgBarCompactLinearUnderlyingValueComparison_transportIso R D F x f
  have hs : (HomotopyLimits.simplicialHomDiagram F x).map f =
      moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap φ) :=
    dgBarCompactStandardSimplicialPostcomp_chainMap R D (F.map f)
  rw [show ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) =
    SSet.opFunctor.map (moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap φ)) from
      congrArg SSet.opFunctor.map hs] at h
  exact dgBarCompactPiZeroChart_naturality_of_comparison
    (dgBarCompactLinearHomPiZeroCohomologyEquiv x (F.obj i))
    (dgBarCompactLinearHomPiZeroCohomologyEquiv x (F.obj j))
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj i))
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj j))
    (moduleUnderlyingSSetMap (dgBarCompactLinearHomCohomologyMap φ))
    (dgBarCompactNativeHomEdgeValue R D x (F.map f)) _ h
    (dgBarCompactLinearHomPiZeroCohomologyEquiv_naturality φ) a

end SerrePositivity.InfinityCategories
