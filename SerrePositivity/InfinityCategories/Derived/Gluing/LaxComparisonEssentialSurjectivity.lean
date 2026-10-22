module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxFixedInputEssentialImage

/-! 元の一般宇宙の導来 lax pullback 比較は、対象について本質的全射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective :
    IsEssentiallySurjective (dgGluingUniverseDerivedNerveLaxComparison R C D M) := by
  intro z
  obtain ⟨a, b, e, he⟩ := dgGluingLaxFixedInputVertex_exists
    (dgGluingUniverseDerivedYoneda.{u, v, w} R C) (dgGluingUniverseDerivedCoefficient R C D M) z
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  obtain ⟨c, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := C)).symm.surjective a
  obtain ⟨d, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := D)).symm.surjective b
  obtain ⟨X, hX⟩ := dgGluingLaxFixedInput_essentialImage R C D M c d e
  refine ⟨ULift.up (Simplex.vertex X), ?_⟩
  rw [← he]
  exact hX

end SerrePositivity.InfinityCategories
