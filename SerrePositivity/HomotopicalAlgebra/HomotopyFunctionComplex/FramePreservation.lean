module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LatchingPreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom

/-! # Left Quillen left adjoints preserve cosimplicial frames

Homotopical constancy follows from Brown's lemma on the actual cofibrant
components. An augmentation over a cofibrant object remains a weak
equivalence. Cofibrancy of that augmentation target is explicit.
-/

@[expose] public section
universe vC uC vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]

lemma cosimplicialFrame_isCofibrant_obj (A : SimplexCategory ⥤ C)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A)) (n : SimplexCategory) :
    IsCofibrant (A.obj n) := by
  have hi : Cofibration ((initial.to A).app n) :=
    ⟨Reedy.cofibration_app simplex (initial.to A) hA n⟩
  exact (isCofibrant_iff_of_isInitial ((initial.to A).app n)
    (initialIsInitial.isInitialObj ((evaluation SimplexCategory C).obj n)
      (⊥_ (SimplexCategory ⥤ C)))).mpr hi

variable {D : Type uD} [Category.{vD} D] [ModelCategory D]
  (L : C ⥤ D) [L.IsLeftAdjoint] [Quillen.IsLeftQuillen L]
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))

include hA in
lemma leftQuillen_frame_reedyCofibrant :
    reedyLeft simplex (cofibrations D) (initial.to (A ⋙ L)) :=
  reedyCofibrant_whiskerRight simplex L A hA

omit [L.IsLeftAdjoint] in
include hA in
lemma leftQuillen_frame_homotopicallyConstant
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {n m : SimplexCategory} (f : n ⟶ m) : weakEquivalences D ((A ⋙ L).map f) := by
  have := cosimplicialFrame_isCofibrant_obj A hA n
  have := cosimplicialFrame_isCofibrant_obj A hA m
  have : WeakEquivalence (A.map f) := ⟨hconst f⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L (A.map f))

omit [L.IsLeftAdjoint] in
include hA in
lemma leftQuillen_frame_augmentation_weakEquivalence {X : C} [IsCofibrant X]
    (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (ha : ∀ n, weakEquivalences C (a.app n)) (n : SimplexCategory) :
    weakEquivalences D ((Functor.whiskerRight a L).app n) := by
  have := cosimplicialFrame_isCofibrant_obj A hA n
  have : IsCofibrant (((Functor.const SimplexCategory).obj X).obj n) :=
    inferInstanceAs (IsCofibrant X)
  have : WeakEquivalence (a.app n) := ⟨ha n⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L (a.app n))

end SerrePositivity.HomotopyFunctionComplex
