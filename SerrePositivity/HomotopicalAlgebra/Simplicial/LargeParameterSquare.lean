module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterMapping
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SelectedTriangle

/-! # Fill a square retaining four selected global homotopies

Two triangles use one common diagonal. All four original homotopies are
retained as entire maps over the parameter K, with no large model.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.LargeParameterSquare

abbrev point {K P : SSet.{r}} (e : K ⟶ P) :
    SSet.stdSimplex.{r}.obj (SimplexCategory.mk 0) ⟶ (ihom K).obj P :=
  curry (fst K _ ≫ e)

lemma edge_zero {K P : SSet.{r}} {e₀ e₁ : K ⟶ P} (H : SSet.Homotopy e₀ e₁) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ curry H.h = point e₀ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, point, uncurry_curry]
  have h : K ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst K _ ≫ SSet.ι₀ := by
    rw [SSet.stdSimplex.δ_one_eq_const]
    rfl
  rw [h, Category.assoc, H.h₀]

lemma edge_one {K P : SSet.{r}} {e₀ e₁ : K ⟶ P} (H : SSet.Homotopy e₀ e₁) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ curry H.h = point e₁ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, point, uncurry_curry]
  have h : K ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst K _ ≫ SSet.ι₁ := by
    rw [SSet.stdSimplex.δ_zero_eq_const]
    rfl
  rw [h, Category.assoc, H.h₁]

/-- Transport an existing homotopy without changing its interval map. -/
def transport {K L P Q : SSet.{r}} (u : K ⟶ L) (q : P ⟶ Q)
    {e₀ e₁ : L ⟶ P} (H : SSet.Homotopy e₀ e₁) :
    SSet.Homotopy (u ≫ e₀ ≫ q) (u ≫ e₁ ≫ q) where
  h := u ▷ SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1) ≫ H.h ≫ q
  h₀ := by rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀_assoc]; rfl
  h₁ := by rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁_assoc]; rfl
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

/-- Change the endpoint expressions using proved equalities, retaining the same map. -/
def changeEndpoints {K P : SSet.{r}} {e₀ e₁ f₀ f₁ : K ⟶ P}
    (H : SSet.Homotopy e₀ e₁) (h₀ : e₀ = f₀) (h₁ : e₁ = f₁) :
    SSet.Homotopy f₀ f₁ := by
  cases h₀
  cases h₁
  exact H

@[simp]
lemma changeEndpoints_h {K P : SSet.{r}} {e₀ e₁ f₀ f₁ : K ⟶ P}
    (H : SSet.Homotopy e₀ e₁) (h₀ : e₀ = f₀) (h₁ : e₁ = f₁) :
    (changeEndpoints H h₀ h₁).h = H.h := by
  cases h₀
  cases h₁
  rfl

variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) {K : SSet.{max w v}}
  {e₀ e₁ e₂ e₃ : K ⟶ UniverseLift.obj.{w} P}
  (H₀₁ : SSet.Homotopy e₀ e₁) (H₁₃ : SSet.Homotopy e₁ e₃)
  (H₀₂ : SSet.Homotopy e₀ e₂) (H₂₃ : SSet.Homotopy e₂ e₃)

abbrev diagonal := LargeParameterHomotopy.homotopy hp e₀ e₃

def leftBoundary : SelectedTriangle.Boundary ((ihom K).obj (UniverseLift.obj.{w} P)) where
  vertex0 := point e₀
  vertex1 := point e₁
  vertex2 := point e₃
  edge01 := curry H₀₁.h
  edge12 := curry H₁₃.h
  edge02 := curry (diagonal hp).h
  edge01_zero := edge_zero H₀₁
  edge01_one := edge_one H₀₁
  edge12_zero := edge_zero H₁₃
  edge12_one := edge_one H₁₃
  edge02_zero := edge_zero (diagonal hp)
  edge02_one := edge_one (diagonal hp)

def rightBoundary : SelectedTriangle.Boundary ((ihom K).obj (UniverseLift.obj.{w} P)) where
  vertex0 := point e₀
  vertex1 := point e₂
  vertex2 := point e₃
  edge01 := curry H₀₂.h
  edge12 := curry H₂₃.h
  edge02 := curry (diagonal hp).h
  edge01_zero := edge_zero H₀₂
  edge01_one := edge_one H₀₂
  edge12_zero := edge_zero H₂₃
  edge12_one := edge_one H₂₃
  edge02_zero := edge_zero (diagonal hp)
  edge02_one := edge_one (diagonal hp)

abbrev boundaryData (left : Bool) := if left then leftBoundary hp H₀₁ H₁₃
  else rightBoundary hp H₀₂ H₂₃

def triangle (left : Bool) : K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 2) ⟶
    UniverseLift.obj.{w} P :=
  uncurry (LargeParameterMapping.fillFaces hp K (boundaryData hp H₀₁ H₁₃ H₀₂ H₂₃ left).faces
    (boundaryData hp H₀₁ H₁₃ H₀₂ H₂₃ left).compatible)

lemma triangle_face (left : Bool) (k : Fin 3) :
    K ◁ SSet.stdSimplex.δ k ≫ triangle hp H₀₁ H₁₃ H₀₂ H₂₃ left =
      uncurry ((boundaryData hp H₀₁ H₁₃ H₀₂ H₂₃ left).faces k) :=
  LargeParameterMapping.fillFaces_uncurry_face hp K _ _ k

lemma left_first : K ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ true = H₀₁.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma left_second : K ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ true = H₁₃.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma right_first : K ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ false = H₀₂.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma right_second : K ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ false = H₂₃.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma common_diagonal :
    K ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hp H₀₁ H₁₃ H₀₂ H₂₃ true =
      K ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hp H₀₁ H₁₃ H₀₂ H₂₃ false := by
  rw [triangle_face, triangle_face]
  rfl

end SerrePositivity.SimplicialModel.LargeParameterSquare
