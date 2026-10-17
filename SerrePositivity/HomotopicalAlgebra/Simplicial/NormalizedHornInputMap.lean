module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CompatibleInputMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison

/-! # Degenerate horn input unions are strictly functorial in the target -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedHornInputMap
variable {K L M : SSet.{v}} {n : ℕ} (i : Fin (n + 2)) (q : K ⟶ L)

lemma boundary_naturality (d : Fin (n + 1)) : DegenerateHornInput.boundary i d K ≫
    (ihom (SSet.horn (n + 1) i).toSSet).map q =
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).map q ≫
      DegenerateHornInput.boundary i d L := by
  dsimp only [DegenerateHornInput.boundary, DegenerateHornInput.degeneracy,
    KanHornFamilyLifting.restriction]
  rw [Category.assoc, ← (pre (SSet.horn (n + 1) i).ι).naturality q,
    ← Category.assoc, ← (pre (SSet.stdSimplex.σ d)).naturality q, Category.assoc]

def map : (NormalizedHornTargetComparison.inputs (K := K) i).toSSet ⟶
    (NormalizedHornTargetComparison.inputs (K := L) i).toSSet :=
  CompatibleInputMap.map
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj L)
    (fun d => DegenerateHornInput.boundary i d K)
    (fun d => DegenerateHornInput.boundary i d L)
    ((ihom (SSet.horn (n + 1) i).toSSet).map q)
    (fun _ => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).map q)
    (boundary_naturality i q)

lemma map_inclusion : map i q ≫ (NormalizedHornTargetComparison.inputs (K := L) i).ι =
    (NormalizedHornTargetComparison.inputs (K := K) i).ι ≫
      (ihom (SSet.horn (n + 1) i).toSSet).map q := rfl

lemma map_id : map i (𝟙 K) = 𝟙 _ := by
  apply (cancel_mono (NormalizedHornTargetComparison.inputs (K := K) i).ι).mp
  rw [map_inclusion, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

lemma map_comp (r : L ⟶ M) : map i q ≫ map i r = map i (q ≫ r) := by
  apply (cancel_mono (NormalizedHornTargetComparison.inputs (K := M) i).ι).mp
  rw [Category.assoc, map_inclusion, ← Category.assoc, map_inclusion,
    map_inclusion, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.SimplicialModel.NormalizedHornInputMap
