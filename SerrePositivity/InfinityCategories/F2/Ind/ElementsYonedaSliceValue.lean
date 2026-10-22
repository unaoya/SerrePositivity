module

public import SerrePositivity.InfinityCategories.F2.Ind.ElementsYonedaSliceFiberMap
public import SerrePositivity.InfinityCategories.F2.Ind.RightFibrationFiberCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：元の Yoneda comma 比較の同値性を、同じ実際の fiber 作用の Yoneda 評価で検査する。
方針：元の同型と証明済みの Yoneda 評価同値を二対三則で外し、right fibration の fiber 判定を使う。
規約：指定値写像の同値性は後続の同じ native 密度余錐の計算で示す。
使われ方：小さい comma 模型から局所 Kan 延長を構成する工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の right fibration は、同じ右ホーン持ち上げにより宇宙を持ち上げても right fibration。 -/
instance rightFibration_ulift_map {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p] :
    RightFibration ((SSet.uliftFunctor.{v, u}).map p) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      have : HasLiftingProperty (horn.{u} (n + 1) i).ι p :=
        RightFibration.mem _ (rightHornInclusions.intro i hi)
      exact HomotopyLimits.ulift_hasLiftingProperty_horn p n i

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 元の大域比較そのものの fiber 作用を、元の指定前層値で評価した写像。 -/
def presheafElementsYonedaSliceValue (x : C _⦋0⦌) :=
  presheafElementsYonedaSliceMapping F x ≫ yonedaPresheafEvaluation x F

/-- 指定値での同じ評価が同値なら、元の fiber 作用自体も同値。 -/
lemma presheafElementsYonedaSliceFiberMap_isQCatEquivalence (x : C _⦋0⦌)
    (hx : IsQCatEquivalence (presheafElementsYonedaSliceValue F x)) :
    IsQCatEquivalence (presheafElementsYonedaSliceFiberMap F x) := by
  have hm : IsQCatEquivalence (presheafElementsYonedaSliceMapping F x) :=
    (yonedaPresheafEvaluation_isQCatEquivalence x F).cancel_right hx
  exact (qCatEquivalenceOfIso (presheafYonedaSliceFiberMappingIso F x)).isQCatEquivalence.cancel_right hm

/-- 元の全空間比較の同値性は、同じ指定値写像の全対象での同値性から従う。 -/
lemma presheafElementsYonedaSliceComparison_isQCatEquivalence_of_values
    (hF : ∀ x : C _⦋0⦌, IsQCatEquivalence (presheafElementsYonedaSliceValue F x)) :
    IsQCatEquivalence (presheafElementsYonedaSliceComparison F) := by
  apply isQCatEquivalence_of_rightFibration_fibers
    ((SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F))
    (presheafYonedaSliceProjection F) (presheafElementsYonedaSliceComparison F)
    (presheafElementsYonedaSliceComparison_projection F)
  rintro ⟨x⟩
  exact (qCatEquivalenceOfIso
    (uliftVertexFiberIso.{u, u + 1} (smallRightUnstraighteningProjection F) x)).isQCatEquivalence.cancel_left
      (presheafElementsYonedaSliceFiberMap_isQCatEquivalence F x (hF x))

end SerrePositivity.InfinityCategories.F2.Ind
