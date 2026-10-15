module

public import SerrePositivity.HomotopicalAlgebra.Localization.FibrantMappingTests
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-! # Derived inversion of test maps makes right-adjoint values local

Apply the left Quillen functor to the actual cofibrant source resolution.
For maps between cofibrant objects its augmentation remains weak, so a
weak image of the test map gives a weak map of resolution Hom. Transport
along the adjunction in independent Hom universes and remove the target
replacement. Arbitrary test maps are then handled by the specified Q.
-/

@[expose] public section
universe vC uC vD uD
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [Quillen.IsLeftQuillen L]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [ModelCategory SSet.{vC}] [ModelCategory SSet.{vD}] [ModelCategory SSet.{max vC vD}]
  (hcofC : cofibrations SSet.{vC} = MorphismProperty.monomorphisms _)
  (hfibC : fibrations SSet.{vC} = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (hcofD : cofibrations SSet.{vD} = MorphismProperty.monomorphisms _)
  (hfibD : fibrations SSet.{vD} = SSet.modelCategoryQuillen.J.{vD}.rlp)
  (hcofB : cofibrations SSet.{max vC vD} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vD} = SSet.modelCategoryQuillen.J.{max vC vD}.rlp)

include adj hcofC hfibC hcofD hfibD hcofB hfibB in
lemma mappingTest_rightAdjoint_of_cofibrant {X Z : C} [IsCofibrant X] [IsCofibrant Z]
    (f : X ⟶ Z) (hf : weakEquivalences D (L.map f)) (Y : D) [IsFibrant Y] :
    mappingTest.{vC, uC} (C := C) cof fib (R.obj Y) f := by
  have : L.IsLeftAdjoint := ⟨R, ⟨adj⟩⟩
  have : R.IsRightAdjoint := ⟨L, ⟨adj⟩⟩
  have := Quillen.isRightQuillen_of_isLeftQuillen adj
  have := Quillen.isFibrant_obj R Y
  let q := cosimplicialResolutionFamily cof
  let a := q.obj.map f
  have ha (n : SimplexCategory) : weakEquivalences D (L.map (a.app n)) := by
    have hX := leftQuillen_frame_augmentation_weakEquivalence L (q.obj.obj X) (q.cofibrant X)
      (q.augmentation.app X) (fun n => (q.atObject X).augmentation_weakEquivalence n) n
    have hZ := leftQuillen_frame_augmentation_weakEquivalence L (q.obj.obj Z) (q.cofibrant Z)
      (q.augmentation.app Z) (fun n => (q.atObject Z).augmentation_weakEquivalence n) n
    have hn := congr_app (q.augmentation.naturality f) n
    change a.app n ≫ (q.augmentation.app Z).app n = (q.augmentation.app X).app n ≫ f at hn
    apply (weakEquivalences D).of_postcomp _ _ hZ
    have he : L.map (a.app n) ≫ L.map ((q.augmentation.app Z).app n) =
        L.map ((q.augmentation.app X).app n) ≫ L.map f := by
      rw [← L.map_comp, hn, L.map_comp]
    exact he.symm ▸ (weakEquivalences D).comp_mem _ _ hX hf
  have ht := cosimplicialHomMap_weakEquivalence hcofD (Functor.whiskerRight a L)
    (leftQuillen_frame_reedyCofibrant L _ (q.cofibrant X))
    (leftQuillen_frame_reedyCofibrant L _ (q.cofibrant Z)) ha Y
  exact (mappingTest_iff_at_fibrant cof fib hcofC f (R.obj Y)).mpr
    ((adjunction_cosimplicialHomMap_weakEquivalence_iff adj hcofC hfibC hcofD hfibD
      hcofB hfibB a Y).mp ht)

include adj hcofC hfibC hcofD hfibD hcofB hfibB in
lemma rightAdjoint_local_of_cofibrant_test (S : MorphismProperty C)
    (hS : ∀ {X Z : C} (f : X ⟶ Z), S f →
      weakEquivalences D (L.map ((cofibrantSource cof).map f)))
    (Y : D) [IsFibrant Y] : localObjects.{vC, uC} (C := C) cof fib S (R.obj Y) := by
  intro X Z f hf
  have := cofibrantSource_isCofibrant cof X
  have := cofibrantSource_isCofibrant cof Z
  have ht := mappingTest_rightAdjoint_of_cofibrant adj cof fib hcofC hfibC hcofD hfibD
    hcofB hfibB ((cofibrantSource cof).map f) (hS f hf) Y
  exact (mappingTest_arrow_iff cof fib hcofC (R.obj Y)
    (Arrow.homMk ((cofibrantSourceComparison cof).app X)
      ((cofibrantSourceComparison cof).app Z) ((cofibrantSourceComparison cof).naturality f).symm)
    (cofibrantSourceComparison_trivialFibration cof X).2
    (cofibrantSourceComparison_trivialFibration cof Z).2).mp ht

end SerrePositivity.Bousfield
