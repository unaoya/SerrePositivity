module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing

/-! # Boundary fillers for whole large-parameter mapping spaces

Every dimension is filled at once over the entire parameter object. The
uncurried extension retains the prescribed boundary, including any
previously selected global homotopies encoded there. No model structure
in the larger universe is needed.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.LargeParameterMapping

instance boundaryMono (K : SSet.{r}) (d : ℕ) : Mono (K ◁ (SSet.boundary.{r} d).ι) := by
  have : ∀ n, Mono ((K ◁ (SSet.boundary.{r} d).ι).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun x y h => by
      change (x.1, x.2.val) = (y.1, y.2.val) at h
      apply Prod.ext
      · exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk d)).obj n => z.1) h
      · apply Subtype.ext
        exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk d)).obj n => z.2) h)
  exact NatTrans.mono_of_mono_app _

variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) (K : SSet.{max w v})

def fill (d : ℕ)
    (b : (SSet.boundary.{max w v} d).toSSet ⟶ (ihom K).obj (UniverseLift.obj.{w} P)) :
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk d) ⟶
      (ihom K).obj (UniverseLift.obj.{w} P) :=
  curry (LargeParameterExtension.extend hp (K ◁ (SSet.boundary.{max w v} d).ι) (uncurry b))

lemma fill_boundary (d : ℕ)
    (b : (SSet.boundary.{max w v} d).toSSet ⟶ (ihom K).obj (UniverseLift.obj.{w} P)) :
    (SSet.boundary.{max w v} d).ι ≫ fill hp K d b = b := by
  apply uncurry_injective
  rw [uncurry_natural_left, fill, uncurry_curry, LargeParameterExtension.extend_initial]

include hp in
/-- Boundary data in the mapping space retain all maps on the whole parameter K. -/
lemma fillers : UniverseLift.BoundaryFillers ((ihom K).obj (UniverseLift.obj.{w} P)) :=
  fun d b => ⟨fill hp K d b, fill_boundary hp K d b⟩

/-- Fill a compatible collection of already specified global faces in any dimension ≥ 2. -/
def fillFaces {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (UniverseLift.obj.{w} P))) (hf : BoundaryGluing.StandardCompatible f) :
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 2)) ⟶
      (ihom K).obj (UniverseLift.obj.{w} P) :=
  fill hp K (n + 2) (BoundaryGluing.standardDesc f hf)

lemma fillFaces_face {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (UniverseLift.obj.{w} P))) (hf : BoundaryGluing.StandardCompatible f)
    (k : Fin (n + 3)) :
    SSet.stdSimplex.δ k ≫ fillFaces hp K f hf = f k := by
  rw [← SSet.boundary.ι_ι, Category.assoc, fillFaces, fill_boundary,
    BoundaryGluing.standardDesc_fac]

/-- The exact prescribed face is retained as a map on K, before currying. -/
lemma fillFaces_uncurry_face {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (UniverseLift.obj.{w} P))) (hf : BoundaryGluing.StandardCompatible f)
    (k : Fin (n + 3)) :
    K ◁ SSet.stdSimplex.δ k ≫ uncurry (fillFaces hp K f hf) = uncurry (f k) := by
  rw [← uncurry_natural_left, fillFaces_face]

end SerrePositivity.SimplicialModel.LargeParameterMapping
