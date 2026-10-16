module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Actual simplicial fibers over discrete labels and maps between them -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiscreteFiber
variable {I : Type v} {X Y : SSet.{v}}

lemma label_naturality (b : X ⟶ PiZeroConstant.discrete I)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : X.obj n) :
    b.app m (X.map θ x) = b.app n x :=
  types_congr_hom (b.naturality θ) x

def obj (b : X ⟶ PiZeroConstant.discrete I) (i : I) : SSet.{v} where
  obj n := {x : X.obj n // b.app n x = i}
  map θ := ↾fun x => ⟨X.map θ x.1, (label_naturality b θ x.1).trans x.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (X.map_id n) x.1
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (X.map_comp f g) x.1

def inclusion (b : X ⟶ PiZeroConstant.discrete I) (i : I) : obj b i ⟶ X where
  app _ := ↾Subtype.val
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def map (j : X ⟶ Y) (b : Y ⟶ PiZeroConstant.discrete I) (i : I) :
    obj (j ≫ b) i ⟶ obj b i where
  app _ := ↾fun x => ⟨j.app _ x.1, x.2⟩
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (j.naturality θ) x.1

instance map_mono (j : X ⟶ Y) [Mono j] (b : Y ⟶ PiZeroConstant.discrete I) (i : I) :
    Mono (map j b i) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  apply (mono_iff_injective _).mpr
  intro x y h
  apply Subtype.ext
  exact (mono_iff_injective (j.app n)).mp inferInstance (congrArg Subtype.val h)

end SerrePositivity.SimplicialModel.DiscreteFiber
