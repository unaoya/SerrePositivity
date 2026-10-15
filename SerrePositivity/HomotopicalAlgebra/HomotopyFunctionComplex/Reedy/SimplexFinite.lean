module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOpposite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.Basic.Finite.Sigma

/-! # Finite latching and matching diagrams for the simplex category

These instances discharge the particular limit/colimit hypotheses in any
finitely complete and finitely cocomplete source; cocompleteness of arbitrary
size is not required for the simplex objects.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial

namespace SerrePositivity.Reedy

abbrev simplexLatchingCode (j : SimplexCategory) (f : LatchingIndex simplex j) :
    Σ n : Fin (j.len + 1), (⦋n.val⦌ ⟶ j) :=
  ⟨⟨f.obj.left.len, Nat.lt_succ_of_le (latching_degree_lt simplex f).le⟩, f.obj.hom⟩

lemma simplexLatchingCode_injective (j : SimplexCategory) :
    Function.Injective (simplexLatchingCode j) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  obtain ⟨x, f, rfl⟩ := Over.mk_surjective f
  obtain ⟨y, g, rfl⟩ := Over.mk_surjective g
  have hxy : x = y := SimplexCategory.ext (congrArg (fun a ↦ a.1.val) h)
  subst y
  have hfg : f = g := eq_of_heq (Sigma.mk.inj h).2
  subst g
  rfl

abbrev simplexMatchingCode (j : SimplexCategory) (f : MatchingIndex simplex j) :
    Σ n : Fin (j.len + 1), (j ⟶ ⦋n.val⦌) :=
  ⟨⟨f.obj.right.len, Nat.lt_succ_of_le (matching_degree_lt simplex f).le⟩, f.obj.hom⟩

lemma simplexMatchingCode_injective (j : SimplexCategory) :
    Function.Injective (simplexMatchingCode j) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  obtain ⟨x, f, rfl⟩ := Under.mk_surjective f
  obtain ⟨y, g, rfl⟩ := Under.mk_surjective g
  have hxy : x = y := SimplexCategory.ext (congrArg (fun a ↦ a.1.val) h)
  subst y
  have hfg : f = g := eq_of_heq (Sigma.mk.inj h).2
  subst g
  rfl

instance simplexLatchingIndex_finite (j : SimplexCategory) : Finite (LatchingIndex simplex j) :=
  Finite.of_injective _ (simplexLatchingCode_injective j)

instance simplexMatchingIndex_finite (j : SimplexCategory) : Finite (MatchingIndex simplex j) :=
  Finite.of_injective _ (simplexMatchingCode_injective j)

instance simplexLatchingHom_finite (j : SimplexCategory) (f g : LatchingIndex simplex j) :
    Finite (f ⟶ g) := Finite.of_injective (fun φ : f ⟶ g ↦ φ.hom.left) (by
      intro φ ψ h
      apply ObjectProperty.hom_ext
      exact Over.OverMorphism.ext h)

instance simplexMatchingHom_finite (j : SimplexCategory) (f g : MatchingIndex simplex j) :
    Finite (f ⟶ g) := Finite.of_injective (fun φ : f ⟶ g ↦ φ.hom.right) (by
      intro φ ψ h
      apply ObjectProperty.hom_ext
      exact Under.UnderMorphism.ext h)

instance simplexLatchingIndex_finCategory (j : SimplexCategory) :
    FinCategory (LatchingIndex simplex j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

instance simplexMatchingIndex_finCategory (j : SimplexCategory) :
    FinCategory (MatchingIndex simplex j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

instance simplexOpLatchingIndex_finite (j : SimplexCategoryᵒᵖ) :
    Finite (LatchingIndex simplexOp j) :=
  Finite.of_equiv (MatchingIndex simplex j.unop) (latchingOpObjEquiv simplex j.unop).symm

instance simplexOpMatchingIndex_finite (j : SimplexCategoryᵒᵖ) :
    Finite (MatchingIndex simplexOp j) :=
  Finite.of_equiv (LatchingIndex simplex j.unop) (matchingOpObjEquiv simplex j.unop).symm

instance simplexOpLatchingHom_finite (j : SimplexCategoryᵒᵖ) (f g : LatchingIndex simplexOp j) :
    Finite (f ⟶ g) := Finite.of_injective (fun φ : f ⟶ g ↦ φ.hom.left.unop) (by
      intro φ ψ h
      apply ObjectProperty.hom_ext
      exact Over.OverMorphism.ext (Quiver.Hom.unop_inj h))

instance simplexOpMatchingHom_finite (j : SimplexCategoryᵒᵖ) (f g : MatchingIndex simplexOp j) :
    Finite (f ⟶ g) := Finite.of_injective (fun φ : f ⟶ g ↦ φ.hom.right.unop) (by
      intro φ ψ h
      apply ObjectProperty.hom_ext
      exact Under.UnderMorphism.ext (Quiver.Hom.unop_inj h))

instance simplexOpLatchingIndex_finCategory (j : SimplexCategoryᵒᵖ) :
    FinCategory (LatchingIndex simplexOp j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

instance simplexOpMatchingIndex_finCategory (j : SimplexCategoryᵒᵖ) :
    FinCategory (MatchingIndex simplexOp j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

end SerrePositivity.Reedy
