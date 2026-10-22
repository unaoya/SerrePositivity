module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedInputSectionFactorization
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionPathFactorization
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputPathTransport

/-! 保存済みの入力付き実比較は、同じ係数 path 比較と具体的入力切断による輸送の合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open HomotopyLimits
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedCompositionInputPair_section (X Y : DGGluingObject R C D M) :
    lift (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
        (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
            (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) ≫
        dgGluingDerivedCompositionInputPairSection R C D M X Y := by
  have hn :
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
            (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) ≫
        (uliftTensorIso _ _).hom =
      lift ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := rfl
  rw [dgGluingDerivedCompositionInputPairSection, ← Category.assoc, hn]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc]
    exact dgGluingHomDerivedLastCompositionInputLift_factor R C D M X Y
  · simp only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc]
    exact dgGluingHomDerivedFirstCompositionInputLift_factor R C D M X Y

lemma dgGluingHomDerivedCompositionInputPathComparison_factor
    (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionInputPathComparison R C D M X Y =
      dgGluingDerivedHomCoefficientPathComparison R C D M X Y ≫
        dgGluingDerivedCompositionInputPathTransport R C D M X Y := by
  apply pullback.hom_ext
  · rw [dgGluingHomDerivedCompositionInputPathComparison_path R C D M X Y,
      Category.assoc, dgGluingDerivedCompositionInputPathTransport_path R C D M X Y,
      ← Category.assoc, dgGluingDerivedHomCoefficientPathComparison_path R C D M X Y,
      dgGluingHomDerivedCompositionDiagonalPath_factor R C D M X Y]
  · rw [dgGluingHomDerivedCompositionInputPathComparison_compositions R C D M X Y,
      Category.assoc, dgGluingDerivedCompositionInputPathTransport_inputs R C D M X Y,
      ← Category.assoc, dgGluingDerivedHomCoefficientPathComparison_inputs R C D M X Y,
      dgGluingHomDerivedCompositionInputPair_section R C D M X Y]

end SerrePositivity.InfinityCategories
