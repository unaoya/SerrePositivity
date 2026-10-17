module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CompatibleInputUnion

/-! # A map of input families induces a map on their small unions -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.CompatibleInputMap
variable {J : Type u} {B D : SSet.{v}} (S T : J → SSet.{v})
  (b : ∀ j, S j ⟶ B) (c : ∀ j, T j ⟶ D)
  (q : B ⟶ D) (t : ∀ j, S j ⟶ T j) (h : ∀ j, b j ≫ q = t j ≫ c j)

def map : (CompatibleInputUnion.inputs S b).toSSet ⟶
    (CompatibleInputUnion.inputs T c).toSSet where
  app m := ↾fun x => ⟨q.app m x.val, by
    obtain ⟨j, y, hy⟩ := (CompatibleInputUnion.mem_inputs S b m x.val).mp x.property
    apply (CompatibleInputUnion.mem_inputs T c m _).mpr
    refine ⟨j, (t j).app m y, ?_⟩
    exact (types_congr_hom (congr_app (h j) m) y).symm.trans (congrArg (q.app m) hy)⟩
  naturality {m n} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (q.naturality θ) x.val

lemma map_inclusion : map S T b c q t h ≫ (CompatibleInputUnion.inputs T c).ι =
    (CompatibleInputUnion.inputs S b).ι ≫ q := rfl

lemma toInputs_map (j : J) : CompatibleInputUnion.toInputs S b j ≫ map S T b c q t h =
    t j ≫ CompatibleInputUnion.toInputs T c j := by
  apply (cancel_mono (CompatibleInputUnion.inputs T c).ι).mp
  rw [Category.assoc, map_inclusion, ← Category.assoc,
    CompatibleInputUnion.toInputs_inclusion, Category.assoc,
    CompatibleInputUnion.toInputs_inclusion]
  exact h j

end SerrePositivity.SimplicialModel.CompatibleInputMap
