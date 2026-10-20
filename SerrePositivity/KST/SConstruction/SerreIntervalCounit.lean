module
public import SerrePositivity.KST.SConstruction.SerreIntervalDiagonalEndpoints
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation

/-! # 元の鎖区間の Serre 対角の余単位律
概要：増大写像を Serre 対角の左右に適用すると、元の区間の恒等射を回収する。
方針：零頂点と辺で射を判定し、元の単位生成元上の左右 unitor を使う。
規約：元の単位比較射を保持する。使われ方：cubical tensor 比較の単位保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の零頂点の増大は、単位複体の元の生成元。 -/
lemma serreIntervalAugmentation_zero_value :
    (serreIntervalAugmentation A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) :=
  congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalAugmentation_zero A)

/-- 元の一頂点の増大も、単位複体の同じ生成元。 -/
lemma serreIntervalAugmentation_one_value :
    (serreIntervalAugmentation A).f 0 (cycleFromUnit _ (serreIntervalOne A)).val =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) :=
  congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalAugmentation_one A)

/-- Serre 対角と元の増大写像は、元の左単位射に沿う余単位律を満たす。 -/
lemma serreIntervalDiagonal_left_counit :
    serreIntervalDiagonal A ≫ (serreIntervalAugmentation A ⊗ₘ 𝟙 (serreInterval A)) ≫
        (λ_ (serreInterval A)).hom = 𝟙 _ := by
  apply serreInterval_hom_ext A
  · apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (λ_ (serreInterval A)).hom.f 0
        ((serreIntervalAugmentation A ⊗ₘ 𝟙 (serreInterval A)).f 0
          ((serreIntervalDiagonal A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val)) = _
    rw [serreIntervalDiagonal_zero_value, tensorMap_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalAugmentation_zero_value]
    exact leftUnitor_hom_generator _ 0 _
  · change (λ_ (serreInterval A)).hom.f (-1)
        ((serreIntervalAugmentation A ⊗ₘ 𝟙 (serreInterval A)).f (-1)
          ((serreIntervalDiagonal A).f (-1) (serreIntervalEdge A))) = serreIntervalEdge A
    simp only [serreIntervalDiagonal_edge, serreIntervalDiagonalEdge, map_add]
    rw [tensorMap_apply, tensorMap_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalAugmentation_zero_value,
      serreIntervalAugmentation_edge, TensorProduct.zero_tmul, map_zero, add_zero]
    exact leftUnitor_hom_generator _ (-1) _

/-- Serre 対角と元の増大写像は、元の右単位射に沿う余単位律を満たす。 -/
lemma serreIntervalDiagonal_right_counit :
    serreIntervalDiagonal A ≫ (𝟙 (serreInterval A) ⊗ₘ serreIntervalAugmentation A) ≫
        (ρ_ (serreInterval A)).hom = 𝟙 _ := by
  apply serreInterval_hom_ext A
  · apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (ρ_ (serreInterval A)).hom.f 0
        ((𝟙 (serreInterval A) ⊗ₘ serreIntervalAugmentation A).f 0
          ((serreIntervalDiagonal A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val)) = _
    rw [serreIntervalDiagonal_zero_value, tensorMap_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalAugmentation_zero_value]
    exact rightUnitor_hom_generator _ 0 _
  · change (ρ_ (serreInterval A)).hom.f (-1)
        ((𝟙 (serreInterval A) ⊗ₘ serreIntervalAugmentation A).f (-1)
          ((serreIntervalDiagonal A).f (-1) (serreIntervalEdge A))) = serreIntervalEdge A
    simp only [serreIntervalDiagonal_edge, serreIntervalDiagonalEdge, map_add]
    rw [tensorMap_apply, tensorMap_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalAugmentation_one_value,
      serreIntervalAugmentation_edge, TensorProduct.tmul_zero, map_zero, zero_add]
    exact rightUnitor_hom_generator _ (-1) _

end SerrePositivity.KST.SConstruction
