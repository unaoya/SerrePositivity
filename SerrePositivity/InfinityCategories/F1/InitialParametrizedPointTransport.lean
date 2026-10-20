module

public import SerrePositivity.InfinityCategories.F1.PointHomIntervalComparison
public import SerrePositivity.InfinityCategories.F1.ParametrizedFiberTransportNaturality
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomActionComparison

/-!
概要：全空間の始対象を指定点として評価した、実際の全区間パラメーターの輸送は同値。
方針：元の全左 Hom の円柱による輸送と比較し、その区間比較の同値を消去する。
規約：元の parametrizedFiberTransport の射そのもの。任意の left fibration に適用する。
使われ方：始点固定の Tw の恒等点からの輸送を、Yoneda の実際の区間 Hom 作用で判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の左 Hom 円柱による指定点の作用は、同じ区間比較後の普遍輸送の評価と関手同型。 -/
def pointHomTransportActionAt_parametrizedIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a b : B _⦋0⦌) (v : (vertexFiber p a) _⦋0⦌) :
    FunctorIso (HomotopyLimits.pointHomTransportActionAt p a b v)
      (pointHomIntervalComparison a b ≫
        parametrizedFiberTransport p a b ≫ evaluateFunctorAt v) := by
  have h := ((HomotopyLimits.pointHomFiberTransport p a b).mapIso_parametrized p
    (HomotopyLimits.pointHomBasePrism a b) (HomotopyLimits.pointHomBasePrism_zero a b)
    (HomotopyLimits.pointHomBasePrism_one a b)).postcomp (evaluateFunctorAt v)
  have he : (HomotopyLimits.pointHomFiberTransport p a b).map ≫ evaluateFunctorAt v =
      HomotopyLimits.pointHomTransportActionAt p a b v := by
    rw [FiberTransportFamily.map, curry_evaluateFunctorAt_vertex]
    rfl
  rw [he] at h
  simpa only [pointHomIntervalComparison, Category.assoc] using h

/-- 全空間の始対象を指定点とする、同じ全区間パラメーターの普遍輸送の評価は同値。 -/
lemma parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialVertex
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (d : E _⦋0⦌) (hd : IsInitialVertex d) (b : B _⦋0⦌) :
    IsQCatEquivalence
      (parametrizedFiberTransport p (p.app (Opposite.op ⦋0⦌) d) b ≫
        evaluateFunctorAt (HomotopyLimits.pointHomSourceVertex p d)) := by
  have h₀ := HomotopyLimits.leftFibrationPointHomFamily_homotopyEquivalence p d b hd
  have h := h₀.isQCatEquivalence
  have hA := h.ofFunctorIso (functorIsoOfSimplicialHomotopy
    (HomotopyLimits.pointHomActionComparisonHomotopy p d b))
  have hP := hA.ofFunctorIso (pointHomTransportActionAt_parametrizedIso p
    (p.app (Opposite.op ⦋0⦌) d) b (HomotopyLimits.pointHomSourceVertex p d))
  exact (pointHomIntervalComparison_isQCatEquivalence _ _).cancel_left hP

/-- 同じ指定 fiber の点が全空間の始対象なら、その点での普遍輸送の評価は同値。 -/
lemma parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialFiberPoint
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (a b : B _⦋0⦌) (v : (vertexFiber p a) _⦋0⦌) (hv : IsInitialVertex v.val) :
    IsQCatEquivalence (parametrizedFiberTransport p a b ≫ evaluateFunctorAt v) := by
  rcases v with ⟨d, hd⟩
  have ha : p.app (Opposite.op ⦋0⦌) d = a := hd.trans (pinchedConstant_zero a)
  subst a
  exact parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialVertex p d hv b

end SerrePositivity.InfinityCategories
