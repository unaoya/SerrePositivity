module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitCommaRecovery
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomFamilyInitiality
public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitTransportComparison

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
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

def derivedFreeProbeUnitCommaTargetFiberVertex
    (x : (derivedInfinityCategory A) _⦋0⦌) :
    (vertexFiber (F1B.unitCommaFiberProjection (cAlgForgetDerived A) x)
      (derivedFreeProbeVertex A x)) _⦋0⦌ :=
  ⟨derivedFreeProbeUnitCommaVertex A x, by
    rw [pinchedConstant_zero]
    exact derivedFreeProbeUnitCommaVertex_target A x⟩

def derivedFreeProbeUnitCommaTransportMap
    (x : (derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌) :
    intervalMappingSpace (derivedFreeProbeVertex A x) y ⟶
      intervalMappingSpace x ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) y) :=
  parametrizedFiberTransport (F1B.unitCommaFiberProjection (cAlgForgetDerived A) x)
      (derivedFreeProbeVertex A x) y ≫
    evaluateFunctorAt (derivedFreeProbeUnitCommaTargetFiberVertex A x) ≫
      F1B.unitCommaFiberToInterval (cAlgForgetDerived A) x y

lemma derivedFreeProbeUnitCommaVertex_isInitial_of_transportIso
    (x : (derivedInfinityCategory A) _⦋0⦌)
    (h : ∀ y : (CAlg_R A) _⦋0⦌,
      Nonempty (FunctorIso (derivedFreeProbeUnitIntervalMap A x y)
        (derivedFreeProbeUnitCommaTransportMap A x y))) :
    IsInitialVertex (derivedFreeProbeUnitCommaVertex A x) := by
  let p := F1B.unitCommaFiberProjection (cAlgForgetDerived A) x
  have ht (y : (CAlg_R A) _⦋0⦌) : IsQCatEquivalence
      (parametrizedFiberTransport p (derivedFreeProbeVertex A x) y ≫
        evaluateFunctorAt (derivedFreeProbeUnitCommaTargetFiberVertex A x)) := by
    have hc := (derivedFreeProbeUnitIntervalMap_isQCatEquivalence A x y).ofFunctorIso
      (h y).some
    change IsQCatEquivalence ((parametrizedFiberTransport p (derivedFreeProbeVertex A x) y ≫
      evaluateFunctorAt (derivedFreeProbeUnitCommaTargetFiberVertex A x)) ≫
        F1B.unitCommaFiberToInterval (cAlgForgetDerived A) x y) at hc
    exact (qCatEquivalenceOfIso (F1B.unitCommaFiberIntervalIso
      (cAlgForgetDerived A) x y)).isQCatEquivalence.cancel_right hc
  have hi : ∀ (a : (CAlg_R A) _⦋0⦌) (v : (vertexFiber p a) _⦋0⦌),
      (∀ y, IsQCatEquivalence (parametrizedFiberTransport p a y ≫ evaluateFunctorAt v)) →
        IsInitialVertex v.val := by
    intro a v hv
    rcases v with ⟨d, hd⟩
    have ha : p.app (Opposite.op ⦋0⦌) d = a := hd.trans (pinchedConstant_zero a)
    subst a
    apply isInitialVertex_of_pointHomFamily_equivalence p d
    intro y
    let : KanComplex (vertexFiber p y) := vertexFiber_kanComplex_of_leftFibration p y
    have hc := (pointHomIntervalComparison_isQCatEquivalence _ y).comp (hv y)
    have ha := hc.ofFunctorIso (pointHomTransportActionAt_parametrizedIso p _ y
      (pointHomSourceVertex p d)).symm
    exact ha.ofFunctorIso (functorIsoOfSimplicialHomotopy
      (pointHomActionComparisonHomotopy p d y)).symm
  exact hi (derivedFreeProbeVertex A x) (derivedFreeProbeUnitCommaTargetFiberVertex A x) ht

end SerrePositivity.EInfinity.BarrattEccles
