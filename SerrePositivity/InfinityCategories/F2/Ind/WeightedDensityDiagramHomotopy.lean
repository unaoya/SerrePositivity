module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CurryJointHomotopy
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction

/-!
概要：元の weighted 表現可能図式から、元の全添字の共同分類への一つの自然変換。
方針：共同 Hom の同じ全評価を curry し、両端を元の Yoneda と共同分類へ厳密に戻す。
規約：頂点ごとの同型で代用しない。使われ方：大域余極限族の右制限との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)
local notation "W" => weightedNerve (rightFibrationTotalDiagram F)

/-- 同じ共同 Hom の curry は、元の全空間上の元の表現可能図式。 -/
lemma weightedDensity_source_curry :
    curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op W).inv ≫
      twistedElementsHomDiagram (C := C) (weightedDensityProjection F)) =
        (SSet.uliftFunctor.{u + 1, u}).map (weightedDensityProjection F) ≫ yonedaInfinityMap C := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, yonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 同じ共同分類の curry は、元の weighted 添字で制限した元の全分類図式。 -/
lemma weightedDensity_target_curry :
    curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op W).inv ≫
      weightedDensityJointTargetDiagram F) =
        (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
          (rightFibrationTotalDiagram F)) ≫ strictRightWeightedClassification F := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, strictRightWeightedClassification,
    strictLeftWeightedClassification, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 同じ元の weighted 密度図式から、元の全添字上の共同分類への一つの自然変換。 -/
def weightedDensityDiagramHomotopy : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedDensityProjection F) ≫ yonedaInfinityMap C)
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
      (rightFibrationTotalDiagram F)) ≫ strictRightWeightedClassification F) :=
  let h := curryJointHomotopy
    (functorHomotopyPrecomp (weightedDensityJointHomotopy F)
      (HomotopyLimits.uliftTensorIso.{u, u + 1} C.op W).inv)
  { h := h.h
    h₀ := h.h₀.trans (weightedDensity_source_curry F)
    h₁ := h.h₁.trans (weightedDensity_target_curry F)
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }

end SerrePositivity.InfinityCategories.F2.Ind
