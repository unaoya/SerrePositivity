module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartEquivalence
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardClosedPostcomposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearUnderlyingValueComparison
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 線形模型の道に不変な全基点チャート。 -/
def dgBarCompactLinearHomPiChart (x y : D) (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleZeroPiChart (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomModule (R := R) x y) n
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomZeroBaseCohomologyEquiv x y n).toEquiv

/-- 同じ全空間比較から選んだ実逆データ。 -/
def dgBarCompactLinearNativeHomEquivalence (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomModule (R := R) x y))
      ((SSet.uliftFunctor.{max u v + 1, max u v}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor R D x).app
          (Opposite.op ⦋0⦌) (ULift.up
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))))).obj) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearUnderlyingValueComparison_isQCatEquivalence R D x y).choose

/-- native Hom 値の追加宇宙での全基点チャート。 -/
def dgBarCompactNativeHomPiChart (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) (n : ℕ) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomPiChart R D x y n).ofEquivalence
    (dgBarCompactLinearNativeHomEquivalence R D x y)

/-- 元の coherent 辺による native 値の実作用。 -/
def dgBarCompactNativeHomEdgeValue {y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D} (x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D)
    (f : y ⟶ z) :=
  (SSet.uliftFunctor.{max u v + 1, max u v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max u v + 1, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max u v, max u v + 1}
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))))).map
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor R D x)))

lemma dgBarCompactNativeHomPiChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j)
    (n : ℕ) (z) (a) :
    (dgBarCompactNativeHomPiChart R D x (F.obj j) n).equiv
      ((dgBarCompactNativeHomEdgeValue R D x (F.map f)).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (dgBarCompactNativeHomEdgeValue R D x (F.map f)) z a) =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) (F.map f))
        (-((n + 1 : ℕ) : ℤ)) ((dgBarCompactNativeHomPiChart R D x (F.obj i) n).equiv z a) := by
  let φ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) (F.map f)
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearUnderlyingValueComparison_transportIso R D F x f
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ) :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardSimplicialPostcomp_chainMap R D (F.map f)
  rw [show ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) from
      congrArg SSet.opFunctor.map hs] at h
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiChart_naturality_of_comparison
    (dgBarCompactLinearHomPiChart R D x (F.obj i) n)
    (dgBarCompactLinearHomPiChart R D x (F.obj j) n)
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj i))
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj j))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomCohomologyMap φ))
    (dgBarCompactNativeHomEdgeValue R D x (F.map f)) _ h
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomPiCohomologyEquiv_naturality φ n) z a

/-- 同じ実比較を使う native Hom 値の零次数チャート。 -/
def dgBarCompactNativeHomPiZeroChart (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_ofEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomPiZeroCohomologyEquiv x y)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearNativeHomEquivalence R D x y)

lemma dgBarCompactNativeHomPiZeroChart_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ ClosedCategory R D) (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) (a) :
    dgBarCompactNativeHomPiZeroChart R D x (F.obj j)
      (SSet.mapπ₀ (dgBarCompactNativeHomEdgeValue R D x (F.map f)) a) =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) (F.map f)) 0
        (dgBarCompactNativeHomPiZeroChart R D x (F.obj i) a) := by
  let φ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) (F.map f)
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearUnderlyingValueComparison_transportIso R D F x f
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ) :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardSimplicialPostcomp_chainMap R D (F.map f)
  rw [show ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) from
      congrArg SSet.opFunctor.map hs] at h
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_naturality_of_comparison
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomPiZeroCohomologyEquiv x (F.obj i))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomPiZeroCohomologyEquiv x (F.obj j))
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj i))
    (dgBarCompactLinearNativeHomEquivalence R D x (F.obj j))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomCohomologyMap φ))
    (dgBarCompactNativeHomEdgeValue R D x (F.map f)) _ h
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearHomPiZeroCohomologyEquiv_naturality φ) a

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
