module
public import SerrePositivity.KST.Fibration.CoreSingleKanFamily
public import SerrePositivity.KST.Fibration.VerdierNullContractionCoordinates

/-!
概要：指定 Verdier 二胞体と零化円柱を、元の core S の全 Kan 評価で比較する。
方針：実合成端を固定する比較を全 Hom に送り、二重パラメータのまま評価する。
規約：元の指定二胞体・実合成端と全比較時刻を保持する。
使われ方：元の商核四角形と指定 Verdier 四角形との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem coreKanUncurry_pre {K A B X : SSet.{u}} (i : A ⟶ B) :
    (ihomCurryIso K B X).inv ≫ (pre (K ◁ i)).app X =
      (pre i).app ((ihom K).obj X) ≫ (ihomCurryIso K A X).inv := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 全内部 Hom の相対比較を、同じ固定部分を保つ全評価の相対比較へ移す。 -/
def FixedRestrictionFunctorEdge.uncurryCoreKan {K A B X : SSet.{u}} [Quasicategory X]
    {i : A ⟶ B} {f g : B ⟶ (ihom K).obj X}
    (E : FixedRestrictionFunctorEdge i f g) :
    FixedRestrictionFunctorEdge (K ◁ i) (uncurry f) (uncurry g) where
  edge := E.edge.map ((truncation 2).map (ihomCurryIso K B X).inv)
  invertible := E.invertible.map _
  restriction := by
    have hn := congrArg (fun m => m.app (Opposite.op ⦋1⦌) E.edge.edge)
      (coreKanUncurry_pre (K := K) (X := X) i)
    change _ = (ihomCurryIso K A X).inv.app (Opposite.op ⦋1⦌)
      (((pre i).app _).app (Opposite.op ⦋1⦌) E.edge.edge) at hn
    rw [E.restriction] at hn
    exact hn

private theorem coreKanEvaluation_heq {A C A' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hC : C = C')
    (f : (Δ[1] : SSet.{u}) ⟶ ((show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) ⟶[SSet.{u}]
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)))
    (g : (Δ[1] : SSet.{u}) ⟶ ((show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A') ⟶[SSet.{u}]
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C'))) (hfg : HEq f g) :
    HEq (uncurry (f ≫ stableCoreSingleKanEnrichedFunctor.map
        (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)))
      (uncurry (g ≫ stableCoreSingleKanEnrichedFunctor.map
        (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A') (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C'))) := by
  cases hA
  cases hC
  have he := eq_of_heq hfg
  rw [he]

/-- 指定二胞体との比較は、元の core S の全 Kan Hom で実合成端を固定する。 -/
def verdierNullContractionCoreKanComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge (stdSimplex.δ (0 : Fin 2))
      (verdierNullContractionFamily d ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (verdierNullPathFamily d 1 ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  (verdierNullContractionComparison d).postcomp _

/-- 同じ比較の二重パラメータを、元の core S 実現の Kan 値で全評価する。 -/
def verdierNullContractionCoreKanEvaluation (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  uncurry (verdierNullContractionCoreKanComparison d).prism

/-- 同じ実比較辺を内部 uncurry し、全円柱の同じ端点間の実可逆辺を得る。 -/
def verdierNullContractionCoreKanCylinderEdge (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    Truncated.Edge
      (X := (truncation 2).obj ((ihom
        ((stableCoreSingleKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ⊗
          (Δ[1] : SSet.{u}))).obj
          (stableCoreSingleKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry (verdierNullContractionFamily d ≫
        stableCoreSingleKanEnrichedFunctor.map _ _)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry (verdierNullPathFamily d 1 ≫
        stableCoreSingleKanEnrichedFunctor.map _ _))) :=
  (verdierNullContractionCoreKanComparison d).edge.map
    ((truncation 2).map (ihomCurryIso
      (stableCoreSingleKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj
      (Δ[1] : SSet.{u})
      (stableCoreSingleKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj).inv)

/-- 全円柱の同じ実比較辺は、全関手空間で可逆である。 -/
theorem verdierNullContractionCoreKanCylinderEdge_isInvertible (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (verdierNullContractionCoreKanCylinderEdge d) :=
  (verdierNullContractionCoreKanComparison d).invertible.map _

/-- 内部 uncurry 後も、全円柱の実合成端上で比較辺は同じ恒等辺に制限される。 -/
def verdierNullContractionCoreKanCylinderComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge
      ((stableCoreSingleKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
        stdSimplex.δ (0 : Fin 2))
      (uncurry (verdierNullContractionFamily d ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)))
      (uncurry (verdierNullPathFamily d 1 ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))) :=
  (verdierNullContractionCoreKanComparison d).uncurryCoreKan

/-- 全円柱の同型は、点ごとの比較を選び直さず同じ実比較辺から得られる。 -/
def verdierNullContractionCoreKanCylinderIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (uncurry (verdierNullContractionFamily d ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)))
      (uncurry (verdierNullPathFamily d 1 ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))) := by
  letI : IsIso (Truncated.HomotopyCategory.homMk
      (verdierNullContractionCoreKanCylinderEdge d)) :=
    verdierNullContractionCoreKanCylinderEdge_isInvertible d
  exact asIso (Truncated.HomotopyCategory.homMk (verdierNullContractionCoreKanCylinderEdge d))

/-- 全評価の始点は、元の core S 零化円柱の同じ Kan 評価。 -/
theorem verdierNullContractionCoreKanEvaluation_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((stableCoreSingleKanObject
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})) ≫ verdierNullContractionCoreKanEvaluation d =
    uncurry (verdierNullContractionFamily d ≫ stableCoreSingleKanEnrichedFunctor.map
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) := by
  rw [verdierNullContractionCoreKanEvaluation, ← uncurry_natural_left,
    FixedRestrictionFunctorEdge.prism_zero]

/-- 全評価の終点は、指定下側二胞体の元の path 族の同じ Kan 評価。 -/
theorem verdierNullContractionCoreKanEvaluation_one (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((stableCoreSingleKanObject
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u})) ≫ verdierNullContractionCoreKanEvaluation d =
    uncurry (verdierNullPathFamily d 1 ≫ stableCoreSingleKanEnrichedFunctor.map
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) := by
  rw [verdierNullContractionCoreKanEvaluation, ← uncurry_natural_left,
    FixedRestrictionFunctorEdge.prism_one]

/-- 元の実合成端は、同じ全評価の全比較時刻にわたり厳密に固定される。 -/
theorem verdierNullContractionCoreKanEvaluation_fixed (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((stableCoreSingleKanObject
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
      ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2))) ≫
        verdierNullContractionCoreKanEvaluation d =
    uncurry (snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
      stdSimplex.δ (0 : Fin 2) ≫ verdierNullContractionFamily d ≫
        stableCoreSingleKanEnrichedFunctor.map
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) := by
  rw [verdierNullContractionCoreKanEvaluation, ← uncurry_natural_left,
    FixedRestrictionFunctorEdge.prism_restriction]

/-- 同じ比較の始点は、元の指定包含・商に対する商核零化円柱の Ex∞ 像。 -/
theorem verdierNullContractionCoreKanEvaluation_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence d.inclusion d.projection) :
    HEq (coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        (coreSingleRealizationObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)).obj (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (quotientSKernelNullCylinder h))
      (uncurry (verdierNullContractionFamily d ≫
        stableCoreSingleKanEnrichedFunctor.map
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))) := by
  have he := coreKanEvaluation_heq (verdierNullDiagonal_source d).symm
    (verdierNullDiagonal_target d).symm _ _ (verdierNullContractionFamily_original_heq d h)
  exact (heq_of_eq (quotientSKernelNullCylinder_coreKan h)).trans he

/-- 指定上下二胞体の全長 Hom 比較を、元の core S の Kan 値へ送る。 -/
def verdierNullHomCoreKanComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (verdierNullHomFamily d j ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (verdierNullHomFamily d k ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  (verdierNullHomRelativeComparison d j k).postcomp _

/-- 同じ上下二胞体の全評価の比較は、共有対角上で同じ恒等辺を保つ。 -/
def verdierNullHomCoreKanEvaluationComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge
      ((stableCoreSingleKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
        coherentTriangleDirectVertexMap)
      (uncurry (verdierNullHomFamily d j ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)))
      (uncurry (verdierNullHomFamily d k ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))) :=
  (verdierNullHomCoreKanComparison d j k).uncurryCoreKan

end SerrePositivity.KST.Fibration
