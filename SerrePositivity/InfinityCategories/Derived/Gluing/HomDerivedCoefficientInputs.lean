module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientFixedEdges
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso

/-! 元の Hom 上の実導来二入力を、主比較と同じ端点表示の区間 Hom へ正規化する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedLeftCoefficientInput (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      intervalMappingSpace
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.left))) :=
  ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
    dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
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

def dgGluingHomDerivedRightCoefficientInput (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      intervalMappingSpace
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.right)))
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right))) :=
  ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
    dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
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

lemma dgGluingHomDerivedLeftCoefficientInput_uncurry (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedLeftCoefficientInput R C D M X Y) =
      intervalMappingUncurry
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
          dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
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
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
      dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (dgGluingNativeLeftCoefficientInput R C D M X Y))
  exact h.trans (Category.comp_id _)

lemma dgGluingHomDerivedRightCoefficientInput_uncurry (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedRightCoefficientInput R C D M X Y) =
      intervalMappingUncurry
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
          dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
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
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
      dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (dgGluingNativeRightCoefficientInput R C D M X Y))
  exact h.trans (Category.comp_id _)

end SerrePositivity.InfinityCategories
