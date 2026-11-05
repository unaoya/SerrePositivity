module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientInputs

/-! 左右の元 Hom 複体を入力として保持する、主比較と同じ導来二作用。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedLeftCoefficientInput (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left)) ⟶
      intervalMappingSpace
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.left))) :=
  (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (dgGluingNativeLeftCoefficientInput R C D M X Y)) ≫
    intervalMappingPostOfEq (𝟙 ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex (representable R X.left))))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex (representable R Y.left))))
      (by simpa only [NatTrans.id_app, CategoryTheory.id_apply] using
        (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C X.left).symm)
      (by simpa only [NatTrans.id_app, CategoryTheory.id_apply] using
        (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C Y.left).symm)

def dgGluingDerivedRightCoefficientInput (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right)) ⟶
      intervalMappingSpace
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.right)))
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right))) :=
  (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (dgGluingNativeRightCoefficientInput R C D M X Y)) ≫
    intervalMappingPostOfEq (𝟙 ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex (M.rightAt X.right))))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex (M.rightAt Y.right))))
      (by simpa only [NatTrans.id_app, CategoryTheory.id_apply] using
        (dgGluingUniverseDerivedCoefficient_vertex R C D M X.right).symm)
      (by simpa only [NatTrans.id_app, CategoryTheory.id_apply] using
        (dgGluingUniverseDerivedCoefficient_vertex R C D M Y.right).symm)

lemma dgGluingDerivedLeftCoefficientInput_uncurry (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingDerivedLeftCoefficientInput R C D M X Y) =
      intervalMappingUncurry
        (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
            (dgGluingNativeLeftCoefficientInput R C D M X Y)) := by
  have h := intervalMappingPostOfEq_uncurry
    (𝟙 ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex (representable R X.left))))
    ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex (representable R Y.left))))
    (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C X.left).symm
    (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C Y.left).symm
    (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (dgGluingNativeLeftCoefficientInput R C D M X Y))
  exact h.trans (Category.comp_id _)

lemma dgGluingDerivedRightCoefficientInput_uncurry (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingDerivedRightCoefficientInput R C D M X Y) =
      intervalMappingUncurry
        (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
            (dgGluingNativeRightCoefficientInput R C D M X Y)) := by
  have h := intervalMappingPostOfEq_uncurry
    (𝟙 ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex (M.rightAt X.right))))
    ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex (M.rightAt Y.right))))
    (dgGluingUniverseDerivedCoefficient_vertex R C D M X.right).symm
    (dgGluingUniverseDerivedCoefficient_vertex R C D M Y.right).symm
    (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (dgGluingNativeRightCoefficientInput R C D M X Y))
  exact h.trans (Category.comp_id _)

lemma dgGluingHomDerivedLeftCoefficientInput_raw_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLeftCoefficientInput R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
        dgGluingDerivedLeftCoefficientInput R C D M X Y := by
  simp only [dgGluingHomDerivedLeftCoefficientInput, dgGluingDerivedLeftCoefficientInput,
    Category.assoc]

lemma dgGluingHomDerivedRightCoefficientInput_raw_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedRightCoefficientInput R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
        dgGluingDerivedRightCoefficientInput R C D M X Y := by
  simp only [dgGluingHomDerivedRightCoefficientInput, dgGluingDerivedRightCoefficientInput,
    Category.assoc]

end SerrePositivity.InfinityCategories
