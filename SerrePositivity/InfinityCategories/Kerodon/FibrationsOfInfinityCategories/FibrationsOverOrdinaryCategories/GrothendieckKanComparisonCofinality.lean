module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanBarLeftAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanScaffold
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.PrecompositionCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationAnodyne

/-!
概要：元のKan係数の比較と同じ置換単位を固定する延長のleft cofinal性。
方針：同じbar/scaffold正方形の可換性と既存の合成・消去則を使う。
規約：cofinal性だけから元の延長の前合成同値性は主張しない。
使われ方：IS-W2 R03fの最後の全空間の比較の検収。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元のKan係数への全空間の比較射は、同じbar/scaffold正方形からleft cofinal。 -/
theorem grothendieckKanCoefficientMap_isLeftCofinal :
    IsLeftCofinal (grothendieckKanCoefficientMap F) := by
  haveI : ∀ i, KanComplex ((grothendieckKanCoefficients F).obj i) := fun i => by
    change KanComplex (exInfinity.obj (nerve (F.obj i)))
    infer_instance
  haveI : ∀ i, Quasicategory ((grothendieckKanCoefficients F).obj i) := fun _ => inferInstance
  have hs := isLeftCofinal_of_precompositionEquivalence (grothendieckNerveScaffold F)
    (grothendieckNerveScaffold_isPrecompositionEquivalence F)
  have ht := isLeftCofinal_of_precompositionEquivalence (tautScaffold (grothendieckKanCoefficients F))
    (tautScaffold_isPrecompositionEquivalence_of_quasicategory (grothendieckKanCoefficients F))
  have hb := isLeftCofinal_of_leftAnodyne _ (grothendieckKanCoefficientBarMap_leftAnodyne F)
  have h := hb.comp ht
  rw [← grothendieckNerveScaffold_kanCoefficientMap F] at h
  exact hs.cancel_left h

/-- 同じ元の置換単位を固定する任意の延長も、同じ比較射のleft cofinal性を持つ。 -/
theorem grothendieckKanCoefficientLift_isLeftCofinal :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∀ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F → IsLeftCofinal f := by
  dsimp only
  intro f hf
  have hu := isLeftCofinal_of_leftAnodyne _
    (continuousLeftFibrationReplacementUnit_leftAnodyne
      (Over.mk (nerveMap (Grothendieck.forget F))))
  apply hu.cancel_left
  rw [hf]
  exact grothendieckKanCoefficientMap_isLeftCofinal F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
