module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaLeftKanShapeAmbient
public import SerrePositivity.InfinityCategories.F2.Ind.ElementsYonedaSliceEquivalence

/-!
概要：P_Σ の元の左 Kan 添字を、元の小さい元の圏からの同じ密度比較で表す。
方針：既存の Yoneda comma 比較と、全部分圏の厳密な添字同型の逆を合成する。
規約：同じ射影と任意の元の図式への制限を全単体で保持する。
使われ方：sifted 余極限の存在から全局所左 Kan 余極限を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C] (v : (SigmaPresheafInfinity C) _⦋0⦌)

/-- 元の P_Σ 左 Kan 添字の元の射影は right fibration。 -/
instance sigmaLeftKanProjection_rightFibration :
    RightFibration (leftKanProjection (sigmaYonedaInfinityMap C) v) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm v)))⟩

/-- 元の P_Σ 左 Kan 添字は quasicategory。 -/
instance sigmaLeftKanShape_quasicategory :
    Quasicategory (leftKanShape (sigmaYonedaInfinityMap C) v) :=
  quasicategory_of_innerFibration (leftKanProjection (sigmaYonedaInfinityMap C) v)

/-- 元の小さい元の圏から、同じ P_Σ 頂点での元の左 Kan 添字への密度比較。 -/
def sigmaElementsLeftKanComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (smallRightUnstraightening (sigmaPresheafVertexFunctor v)) ⟶
        leftKanShape (sigmaYonedaInfinityMap C) v :=
  presheafElementsYonedaSliceComparison (sigmaPresheafVertexFunctor v) ≫
    (sigmaLeftKanCommaIso v).inv

/-- 同じ元の密度比較自身が同値。 -/
lemma sigmaElementsLeftKanComparison_isQCatEquivalence :
    IsQCatEquivalence (sigmaElementsLeftKanComparison v) :=
  (presheafElementsYonedaSliceComparison_isQCatEquivalence (sigmaPresheafVertexFunctor v)).comp
    (qCatEquivalenceOfIso (sigmaLeftKanCommaIso v).symm).isQCatEquivalence

/-- 同じ比較は、元の小さい元の圏の射影を厳密に保つ。 -/
lemma sigmaElementsLeftKanComparison_projection :
    sigmaElementsLeftKanComparison v ≫ leftKanProjection (sigmaYonedaInfinityMap C) v =
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallRightUnstraighteningProjection (sigmaPresheafVertexFunctor v)) := by
  rw [sigmaElementsLeftKanComparison, Category.assoc, sigmaLeftKanCommaIso_inv_projection,
    presheafElementsYonedaSliceComparison_projection]

/-- 元の任意の図式の制限は、同じ小さい元の圏上の元の図式そのもの。 -/
lemma sigmaElementsLeftKanComparison_diagram {D : SSet.{u + 1}}
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    sigmaElementsLeftKanComparison v ≫ leftKanDiagram (sigmaYonedaInfinityMap C) F₀ v =
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallRightUnstraighteningProjection (sigmaPresheafVertexFunctor v)) ≫ F₀ := by
  rw [leftKanDiagram, ← Category.assoc, sigmaElementsLeftKanComparison_projection]

end SerrePositivity.InfinityCategories.HomotopyLimits
