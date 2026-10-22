module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedNerveStructure
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure

/-! 共通対象宇宙では、一般宇宙の構造変換は先に構成した全単体族の同じ持ち上げ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C] [DGCategory R D]
  (M : Bimodule R C D)

lemma dgGluingUniverseAugmentationPrism_specialization (n : ℕ)
    (s : Simplex R (DGGluingObject R C D M) n) (β : (Δ[1] : SSet) _⦋n⦌) :
    (dgGluingUniverseAugmentationPrism R C D M).app (Opposite.op ⦋n⦌) (ULift.up s, β) =
    ULift.up ((dgGluingAugmentationNerveHomotopy R C D M).h.app
      (Opposite.op ⦋n⦌) (s, β)) := by
  apply ULift.ext
  apply Simplex.ext
  change (dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.map (dgGluingToComma R C D M)) (stdSimplex.objEquiv β).toOrderHom).toSimplexData =
    ((dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.map (dgGluingToComma R C D M)) (stdSimplex.objEquiv β).toOrderHom).toSimplexData.map
        (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R C))).map
        (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R C))
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]

lemma dgGluingUniverseDerivedAugmentationHomotopy_specialization (n : ℕ)
    (s : Simplex R (DGGluingObject R C D M) n) (β : (Δ[1] : SSet) _⦋n⦌) :
    (dgGluingUniverseDerivedAugmentationHomotopy R C D M).h.app
      (Opposite.op ⦋n⦌) (ULift.up s, β) =
    ULift.up ((dgGluingDerivedAugmentationHomotopy R C D M).h.app
      (Opposite.op ⦋n⦌) (s, β)) := by
  change (dgGluingUniverseModuleDerivedComparison.{u, max (u + 1) v, max (u + 1) v} R C).app
      (Opposite.op ⦋n⦌)
      ((dgGluingUniverseAugmentationPrism R C D M).app (Opposite.op ⦋n⦌) (ULift.up s, β)) = _
  rw [dgGluingUniverseAugmentationPrism_specialization]
  rfl

end SerrePositivity.InfinityCategories
