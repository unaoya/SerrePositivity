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

private theorem coreKanEvaluation_heq {A C A' C' : StableCategory.{u}}
    (hA : A = A') (hC : C = C')
    (f : (Δ[1] : SSet.{u}) ⟶ ((show StableQCat from A) ⟶[SSet.{u}]
      (show StableQCat from C)))
    (g : (Δ[1] : SSet.{u}) ⟶ ((show StableQCat from A') ⟶[SSet.{u}]
      (show StableQCat from C'))) (hfg : HEq f g) :
    HEq (uncurry (f ≫ stableCoreSingleKanEnrichedFunctor.map
        (show StableQCat from A) (show StableQCat from C)))
      (uncurry (g ≫ stableCoreSingleKanEnrichedFunctor.map
        (show StableQCat from A') (show StableQCat from C'))) := by
  cases hA
  cases hC
  have he := eq_of_heq hfg
  rw [he]

/-- 指定二胞体との比較は、元の core S の全 Kan Hom で実合成端を固定する。 -/
def verdierNullContractionCoreKanComparison (d : VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge (stdSimplex.δ (0 : Fin 2))
      (verdierNullContractionFamily d ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (verdierNullPathFamily d 1 ≫ stableCoreSingleKanEnrichedFunctor.map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  (verdierNullContractionComparison d).postcomp _

/-- 同じ比較の二重パラメータを、元の core S 実現の Kan 値で全評価する。 -/
def verdierNullContractionCoreKanEvaluation (d : VerdierDiagram.{u}) :=
  uncurry (verdierNullContractionCoreKanComparison d).prism

/-- 全評価の始点は、元の core S 零化円柱の同じ Kan 評価。 -/
theorem verdierNullContractionCoreKanEvaluation_zero (d : VerdierDiagram.{u}) :
    ((stableCoreSingleKanObject
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
      prismEndpoint 0 (Δ[1] : SSet.{u})) ≫ verdierNullContractionCoreKanEvaluation d =
    uncurry (verdierNullContractionFamily d ≫ stableCoreSingleKanEnrichedFunctor.map
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) := by
  rw [verdierNullContractionCoreKanEvaluation, ← uncurry_natural_left,
    FixedRestrictionFunctorEdge.prism_zero]

/-- 全評価の終点は、指定下側二胞体の元の path 族の同じ Kan 評価。 -/
theorem verdierNullContractionCoreKanEvaluation_one (d : VerdierDiagram.{u}) :
    ((stableCoreSingleKanObject
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ◁
      prismEndpoint 1 (Δ[1] : SSet.{u})) ≫ verdierNullContractionCoreKanEvaluation d =
    uncurry (verdierNullPathFamily d 1 ≫ stableCoreSingleKanEnrichedFunctor.map
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) := by
  rw [verdierNullContractionCoreKanEvaluation, ← uncurry_natural_left,
    FixedRestrictionFunctorEdge.prism_one]

/-- 元の実合成端は、同じ全評価の全比較時刻にわたり厳密に固定される。 -/
theorem verdierNullContractionCoreKanEvaluation_fixed (d : VerdierDiagram.{u}) :
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
theorem verdierNullContractionCoreKanEvaluation_original_heq (d : VerdierDiagram.{u})
    (h : IsVerdierSequence d.inclusion d.projection) :
    HEq (coaugmentedTensorRightStrength Comparison.exInfinity Comparison.exInfinityUnit
        (coreSingleRealizationObject (show StableQCat from d.left)).obj (Δ[1] : SSet.{u}) ≫
      Comparison.exInfinity.map (quotientSKernelNullCylinder h))
      (uncurry (verdierNullContractionFamily d ≫
        stableCoreSingleKanEnrichedFunctor.map
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))) := by
  have he := coreKanEvaluation_heq (verdierNullDiagonal_source d).symm
    (verdierNullDiagonal_target d).symm _ _ (verdierNullContractionFamily_original_heq d h)
  exact (heq_of_eq (quotientSKernelNullCylinder_coreKan h)).trans he

end SerrePositivity.KST.Fibration
