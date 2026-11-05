module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonVertexImage
public import SerrePositivity.InfinityCategories.Derived.Gluing.ObjectOfModuleArrow

/-! 同じ二入力を持つ任意の導来 lax 頂点は、元の gluing 対象の像と同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxFixedInput_essentialImage (c : C) (d : D)
    (α : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)).Edge
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex c)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex d)))) :
    ∃ X : DGGluingObject R C D M, Nonempty (VertexIso
      ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X)))
      (dgGluingLaxFixedInputVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)
        (ULift.up (Simplex.vertex c)) (ULift.up (Simplex.vertex d)) α)) := by
  obtain ⟨a, ⟨ha⟩⟩ := dgGluingDerivedModuleArrow_representation R C D M c d α
  let X := dgGluingObjectOfModuleArrow R C D M c d a
  refine ⟨X, ?_⟩
  rw [dgGluingUniverseLaxComparison_vertex_image]
  change Nonempty (VertexIso
    (dgGluingLaxFixedInputVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)
      (ULift.up (Simplex.vertex c)) (ULift.up (Simplex.vertex d))
      (dgGluingDerivedModuleArrow R C D M c d
        (dgGluingAugmentation R C D M (dgGluingObjectOfModuleArrow R C D M c d a)))) _)
  rw [dgGluingObjectOfModuleArrow_augmentation]
  exact ⟨dgGluingLaxFixedInputVertexIso _ _ _ _ ha⟩

end SerrePositivity.InfinityCategories
