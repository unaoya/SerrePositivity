module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Homotopies of large-parameter maps into a lifted small injective space

Small boundary fillers assemble an actual interval homotopy. No model
structure is assumed in the larger universe.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.LargeParameterHomotopy

abbrev boundaryColimit (K : SSet.{r}) : IsColimit (BinaryCofan.mk
    (K ◁ SSet.boundary.ι.{r} (1 : Fin 2)) (K ◁ SSet.boundary.ι (0 : Fin 2))) :=
  mapIsColimitOfPreservesOfIsColimit ((curriedTensor SSet.{r}).obj K)
    (SSet.boundary.ι (1 : Fin 2)) (SSet.boundary.ι (0 : Fin 2))
    HomotopyFunctionComplex.BoundaryOne.isColimit

instance boundaryMono (K : SSet.{r}) : Mono (K ◁ (SSet.boundary.{r} 1).ι) := by
  have : ∀ n, Mono ((K ◁ (SSet.boundary.{r} 1).ι).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun x y h => by
      change (x.1, x.2.val) = (y.1, y.2.val) at h
      apply Prod.ext
      · exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1)).obj n => z.1) h
      · apply Subtype.ext
        exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1)).obj n => z.2) h)
  exact NatTrans.mono_of_mono_app _

abbrev vertexSection (K : SSet.{r}) : K ⟶ K ⊗ SSet.stdSimplex.{r}.obj (SimplexCategory.mk 0) :=
  lift (𝟙 K) (SSet.stdSimplex.isTerminalObj₀.from K)

lemma section_zero (K : SSet.{r}) :
    vertexSection K ≫ K ◁ SSet.stdSimplex.δ (1 : Fin 2) = SSet.ι₀ := by
  rw [SSet.stdSimplex.δ_one_eq_const]
  rfl

lemma section_one (K : SSet.{r}) :
    vertexSection K ≫ K ◁ SSet.stdSimplex.δ (0 : Fin 2) = SSet.ι₁ := by
  rw [SSet.stdSimplex.δ_zero_eq_const]
  rfl

variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) {K : SSet.{max w v}}
  (e₀ e₁ : K ⟶ UniverseLift.obj.{w} P)

def boundaryMap : K ⊗ (SSet.boundary.{max w v} 1).toSSet ⟶ UniverseLift.obj.{w} P :=
  (boundaryColimit K).desc (BinaryCofan.mk (fst K _ ≫ e₀) (fst K _ ≫ e₁))

@[reassoc]
lemma boundaryMap_zero : K ◁ SSet.boundary.ι (1 : Fin 2) ≫ boundaryMap e₀ e₁ = fst K _ ≫ e₀ :=
  (boundaryColimit K).fac (BinaryCofan.mk (fst K _ ≫ e₀) (fst K _ ≫ e₁)) ⟨WalkingPair.left⟩

@[reassoc]
lemma boundaryMap_one : K ◁ SSet.boundary.ι (0 : Fin 2) ≫ boundaryMap e₀ e₁ = fst K _ ≫ e₁ :=
  (boundaryColimit K).fac (BinaryCofan.mk (fst K _ ≫ e₀) (fst K _ ≫ e₁)) ⟨WalkingPair.right⟩

def hom : K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ⟶ UniverseLift.obj.{w} P :=
  LargeParameterExtension.extend hp (K ◁ (SSet.boundary.{max w v} 1).ι) (boundaryMap e₀ e₁)

lemma face_zero : K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ hom hp e₀ e₁ = fst K _ ≫ e₀ := by
  rw [← SSet.boundary.ι_ι, whiskerLeft_comp, Category.assoc,
    hom, LargeParameterExtension.extend_initial, boundaryMap_zero]

lemma face_one : K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ hom hp e₀ e₁ = fst K _ ≫ e₁ := by
  rw [← SSet.boundary.ι_ι, whiskerLeft_comp, Category.assoc,
    hom, LargeParameterExtension.extend_initial, boundaryMap_one]

@[reassoc]
lemma at_zero : SSet.ι₀ ≫ hom hp e₀ e₁ = e₀ := by
  rw [← section_zero K, Category.assoc, face_zero]
  rfl

@[reassoc]
lemma at_one : SSet.ι₁ ≫ hom hp e₀ e₁ = e₁ := by
  rw [← section_one K, Category.assoc, face_one]
  rfl

def homotopy : SSet.Homotopy e₀ e₁ where
  h := hom hp e₀ e₁
  h₀ := at_zero hp e₀ e₁
  h₁ := at_one hp e₀ e₁
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.SimplicialModel.LargeParameterHomotopy
