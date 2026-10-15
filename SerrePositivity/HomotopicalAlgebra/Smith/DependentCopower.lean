module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Realization of a family of sets by dependent coproducts

This left adjoint turns a family of sets of commutative squares into the
coproduct of generating domains or codomains used by the small-object step.
The hom universe is normalized to the small-object universe in this core API.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.DependentCopower
variable {C : Type u} [Category.{w} C] [HasCoproducts.{w} C]
  {ι : Type w} (A : ι → C)

abbrev index (P : Discrete ι ⥤ Type w) := Σ i, P.obj ⟨i⟩

def realization : (Discrete ι ⥤ Type w) ⥤ C where
  obj P := ∐ (fun x : index P ↦ A x.1)
  map α := Limits.Sigma.map' (fun x ↦ ⟨x.1, α.app ⟨x.1⟩ x.2⟩) (fun _ ↦ 𝟙 _)
  map_id P := by
    apply Sigma.hom_ext
    intro x
    simp
  map_comp α β := by
    apply Sigma.hom_ext
    intro x
    simp

def homFamily : C ⥤ Discrete ι ⥤ Type w where
  obj X := Discrete.functor (fun i ↦ A i ⟶ X)
  map f := Discrete.natTrans (fun ⟨_⟩ ↦ ↾fun g ↦ g ≫ f)
  map_id X := by
    ext ⟨i⟩ g
    simp
  map_comp f g := by
    ext ⟨i⟩ h
    simp [Category.assoc]

def homEquiv (P : Discrete ι ⥤ Type w) (X : C) :
    ((realization A).obj P ⟶ X) ≃ (P ⟶ (homFamily A).obj X) where
  toFun f := Discrete.natTrans (fun ⟨i⟩ ↦ ↾fun x ↦ Sigma.ι (fun z : index P ↦ A z.1) ⟨i, x⟩ ≫ f)
  invFun α := Sigma.desc (fun x ↦ α.app ⟨x.1⟩ x.2)
  left_inv f := by
    apply Sigma.hom_ext
    intro x
    simp
    rfl
  right_inv α := by
    ext ⟨i⟩ x
    simp
    rfl

def adjunction : realization A ⊣ homFamily A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv A
      homEquiv_naturality_left_symm := by
        intro P Q X α β
        change Sigma.desc (fun x : index P ↦ (α ≫ β).app ⟨x.1⟩ x.2) =
          (realization A).map α ≫ Sigma.desc (fun x : index Q ↦ β.app ⟨x.1⟩ x.2)
        apply Sigma.hom_ext
        intro x
        simp [realization]
        rfl
      homEquiv_naturality_right := by
        intro P X Y f g
        ext ⟨i⟩ x
        change Sigma.ι (fun z : index P ↦ A z.1) ⟨i, x⟩ ≫ (f ≫ g) =
          (Sigma.ι (fun z : index P ↦ A z.1) ⟨i, x⟩ ≫ f) ≫ g
        exact (Category.assoc _ _ _).symm }

lemma realization_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (realization A).IsCardinalAccessible κ := by
  have : PreservesColimitsOfSize.{w, w} (realization A) :=
    (adjunction A).leftAdjoint_preservesColimits
  infer_instance

end SerrePositivity.Smith.DependentCopower
