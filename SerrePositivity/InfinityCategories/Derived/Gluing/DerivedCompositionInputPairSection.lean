module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedInputSectionDiagonals
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedLastInputDiagonalFibration

/-! 左右の元 Hom 入力の対から同じ入力付き合成対応への具体的な同値と二対角の一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open HomotopyLimits SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedCompositionInputPairSection (X Y : DGGluingObject R C D M) :=
  (uliftTensorIso
    (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right))).hom ≫
    (dgGluingDerivedLastCompositionInputSection R C D M X Y ⊗ₘ
      dgGluingDerivedFirstCompositionInputSection R C D M X Y)

lemma dgGluingDerivedCompositionInputPairSection_equivalence (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence (dgGluingDerivedCompositionInputPairSection R C D M X Y) := by
  have := F2.kanComplex_tensor
    (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right))
  have := F2.kanComplex_tensor
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left)))
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right)))
  have := dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  have := dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  have := F2.kanComplex_tensor (dgGluingDerivedLastCompositionInputFiber R C D M X Y)
    (dgGluingDerivedFirstCompositionInputFiber R C D M X Y)
  exact (homotopyEquivalence_of_isIso (uliftTensorIso _ _).hom).comp
    (dgGluingProductMap_homotopyEquivalence
      (dgGluingDerivedLastCompositionInputSection_equivalence R C D M X Y)
      (dgGluingDerivedFirstCompositionInputSection_equivalence R C D M X Y))

lemma dgGluingDerivedCompositionInputPairSection_diagonals (X Y : DGGluingObject R C D M) :
    dgGluingDerivedHomCoefficientActions R C D M X Y ≫
        (dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right ⊗ₘ
          dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right) =
      dgGluingDerivedCompositionInputPairSection R C D M X Y ≫
        (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ⊗ₘ
          dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  have hn :
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
            complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) ≫
        (uliftTensorIso _ _).hom =
      (uliftTensorIso _ _).hom ≫
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y)) ⊗ₘ
          (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y))) := rfl
  rw [dgGluingDerivedHomCoefficientActions, dgGluingUniverseHomCoefficientActions,
    dgGluingDerivedCompositionInputPairSection, hn]
  simp only [Category.assoc, tensorHom_comp_tensorHom,
    dgGluingDerivedLastCompositionInputSection_diagonal R C D M X Y,
    dgGluingDerivedFirstCompositionInputSection_diagonal R C D M X Y]

end SerrePositivity.InfinityCategories
