module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedNerveParameterEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedCoslicePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedStrictConeEvaluation

/-!
概要：反転した Hom の end の作用を weighted nerve と実際の coslice の作用へ接続する。
方針：係数図式のパラメータ付き変換に普遍評価の可換式を適用する。
規約：元の図式上の coherent な錐の切断を扱う。錐の図式全体への延長は別工程。
使われ方：HTT 4.2.4.1 の普遍切断点から得られる比較族の幾何的照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 反転した Hom の係数の前合成を、Bousfield–Kan の end の全パラメータの作用にする。 -/
def weightedConeEndPrecomposition (F : I ⥤ C) (x z : C) :
    bousfieldKanHolim (simplicialHomDiagram F z ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom x z).op ⟶
      bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor) :=
  weightedSectionsParameterMap (bousfieldKanWeight I)
    (reflectedHomPrecompositionDiagram F x z)

/-- end の前合成と weighted nerve の実際の前合成は、普遍評価で厳密に一致する。 -/
lemma weightedConeEndPrecomposition_evaluation (F : I ⥤ C) (x z : C) :
    (nerve I ◁ weightedConeEndPrecomposition F x z) ≫
        bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram F x ⋙ SSet.opFunctor) =
      (α_ (nerve I) (bousfieldKanHolim (simplicialHomDiagram F z ⋙ SSet.opFunctor))
        (SimplicialCategory.sHom x z).op).inv ≫
        (bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram F z ⋙ SSet.opFunctor) ▷
          (SimplicialCategory.sHom x z).op) ≫ weightedConePrecompositionMap F x z := by
  simpa only [weightedConeEndPrecomposition, weightedConePrecompositionMap, Category.assoc]
    using bousfieldKanWeightedNerveEvaluation_parameter_map
      (reflectedHomPrecompositionDiagram F x z)

/-- Hom の end の前合成を既存の比較で評価して得られる、実際の coslice の族。 -/
def weightedCosliceEndPrecompositionEvaluation (F : I ⥤ C) (x z : C) :
    (SSet.uliftFunctor.{v, u}).obj
      (nerve I ⊗ (bousfieldKanHolim (simplicialHomDiagram F z ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom x z).op)) ⟶
          sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) :=
  (SSet.uliftFunctor.{v, u}).map ((nerve I ◁ weightedConeEndPrecomposition F x z) ≫
    bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      weightedCosliceComparison F x

/-- end の前合成を評価した族は、係数から構成した coslice の前合成族そのもの。 -/
lemma weightedCosliceEndPrecompositionEvaluation_eq_family (F : I ⥤ C) (x z : C) :
    weightedCosliceEndPrecompositionEvaluation F x z =
      (SSet.uliftFunctor.{v, u}).map
        ((α_ (nerve I) (bousfieldKanHolim (simplicialHomDiagram F z ⋙ SSet.opFunctor))
          (SimplicialCategory.sHom x z).op).inv ≫
          (bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram F z ⋙ SSet.opFunctor) ▷
            (SimplicialCategory.sHom x z).op)) ≫
        (uliftTensorIso _ _).hom ≫ weightedCoslicePrecompositionFamily F x z := by
  simp only [weightedCosliceEndPrecompositionEvaluation,
    weightedConeEndPrecomposition_evaluation, weightedCoslicePrecompositionFamily,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- 既存の coherent 錐の切断比較を前合成して評価すると、同じ coslice の族を回収する。 -/
lemma reflectedHomHolimConeComparison_precomposition_uncurry (F : I ⥤ C) (x z : C) :
    relativeFunctorUncurry
        ((SSet.uliftFunctor.{v, u}).map (weightedConeEndPrecomposition F x z) ≫
          reflectedHomHolimConeComparison F x) =
      (uliftTensorIso _ _).inv ≫ weightedCosliceEndPrecompositionEvaluation F x z := by
  rw [relativeFunctorUncurry_parameter, reflectedHomHolimConeComparison_uncurry]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
