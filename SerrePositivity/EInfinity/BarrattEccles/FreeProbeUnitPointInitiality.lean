module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitCommaRecovery
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.PointHomFamilyInitiality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CommaUnitTransportComparison

/-!
概要：同じ自由単位の comma 候補の始対象性を、その点からの普遍輸送へ還元する。
方針：左 Hom の全族と区間輸送の公開比較を使い、P の局所始対象判定へ渡す。
規約：元の候補自身を使い、自由関手 F と大域単位は入力にしない。
使われ方：標準区間比較と同じ候補の普遍輸送との照合後の g2-2 の出口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

def derivedFreeProbeUnitCommaTargetFiberVertex
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (cAlgForgetDerived A) x)
      (derivedFreeProbeVertex A x)) _⦋0⦌ :=
  ⟨derivedFreeProbeUnitCommaVertex A x, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact derivedFreeProbeUnitCommaVertex_target A x⟩

def derivedFreeProbeUnitCommaTransportMap
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (derivedFreeProbeVertex A x) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (cAlgForgetDerived A) x)
      (derivedFreeProbeVertex A x) y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (derivedFreeProbeUnitCommaTargetFiberVertex A x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval (cAlgForgetDerived A) x y

lemma derivedFreeProbeUnitCommaVertex_isInitial_of_transportIso
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (h : ∀ y : (CAlg_R A) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (derivedFreeProbeUnitIntervalMap A x y)
        (derivedFreeProbeUnitCommaTransportMap A x y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (derivedFreeProbeUnitCommaVertex A x) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (cAlgForgetDerived A) x
  have ht (y : (CAlg_R A) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p (derivedFreeProbeVertex A x) y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (derivedFreeProbeUnitCommaTargetFiberVertex A x)) := by
    have hc := (derivedFreeProbeUnitIntervalMap_isQCatEquivalence A x y).ofFunctorIso
      (h y).some
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p (derivedFreeProbeVertex A x) y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (derivedFreeProbeUnitCommaTargetFiberVertex A x)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval (cAlgForgetDerived A) x y) at hc
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso
      (cAlgForgetDerived A) x y)).isQCatEquivalence.cancel_right hc
  have hi : ∀ (a : (CAlg_R A) _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌),
      (∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p a y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v.val := by
    intro a v hv
    rcases v with ⟨d, hd⟩
    have ha : p.app (Opposite.op ⦋0⦌) d = a := hd.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
    subst a
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isInitialVertex_of_pointHomFamily_equivalence p d
    intro y
    let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p y
    have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointHomIntervalComparison_isQCatEquivalence _ y).comp (hv y)
    have ha := hc.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointHomTransportActionAt_parametrizedIso p _ y
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomSourceVertex p d)).symm
    exact ha.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomActionComparisonHomotopy p d y)).symm
  exact hi (derivedFreeProbeVertex A x) (derivedFreeProbeUnitCommaTargetFiberVertex A x) ht

end SerrePositivity.EInfinity.BarrattEccles
