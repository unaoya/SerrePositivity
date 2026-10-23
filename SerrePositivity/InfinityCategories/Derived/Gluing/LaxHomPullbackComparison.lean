module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomMappingComparison
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMapping

/-! 同じ実 Hom 比較を、F2 の指定された厳密な写像空間引き戻しへ運ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
local notation "F" => dgGluingUniverseDerivedNerveLaxComparison R C D M

def dgGluingLaxHomPullback (X Y : DGGluingObject R C D M) : SSet.{max (u + 1) v w} :=
  pullback
    (pinchedHomMap (F2.arrowEndpointPair
      ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C)))
      ((F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X))))
      ((F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y)))))
    (pinchedHomPullbackBaseMap (F2.arrowEndpointPair
      ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C) ⊗ₘ
        (dgGluingUniverseDerivedCoefficient R C D M))
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))))

def dgGluingLaxHomPullbackComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingLaxHomPullback R C D M X Y :=
  dgGluingLaxHomMappingComparison R C D M X Y ≫
    (F2.laxPullbackMappingIso (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y)))).hom

lemma dgGluingLaxHomPullbackComparison_arrow (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.fst _ _ =
    dgGluingLaxHomMappingComparison R C D M X Y ≫
      pinchedHomMap (F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))) := by
  rw [dgGluingLaxHomPullbackComparison, Category.assoc, F2.laxPullbackMappingIso_arrow]

lemma dgGluingLaxHomPullbackComparison_inputs (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.snd _ _ =
    dgGluingLaxHomMappingComparison R C D M X Y ≫
      pinchedHomMap (pullback.snd (F2.arrowEndpointPair
      ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C) ⊗ₘ
        (dgGluingUniverseDerivedCoefficient R C D M)))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))) := by
  rw [dgGluingLaxHomPullbackComparison, Category.assoc, F2.laxPullbackMappingIso_inputs]

end SerrePositivity.InfinityCategories
