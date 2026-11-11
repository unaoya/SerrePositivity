module
public import SerrePositivity.KST.Fibration.WeakStringFinitePostMap
public import SerrePositivity.KST.Fibration.WeakStringCofiberPostRealization
public import SerrePositivity.KST.Fibration.LocalizedFiniteProductEquality

/-! # 元の全長の有限 W 列比較の包含側の完全関手による後合成の整合性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の同じ初期頂点と全連続 cofiber の有限比較は、全長・全正反復で後合成と整合する。 -/
theorem weakStringFiniteComparison_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakStringPostExact f q ⦋n⦌) ≫
        weakStringFiniteComparison q n (r + 1)) =
      AnodyneHomotopy.anodyneQ.map
        (weakStringFiniteComparison (f ≫ q : A ⟶ C) n (r + 1) ≫
          weakStringFinitePostMap f q n (r + 1)) := by
  unfold weakStringFiniteComparison weakStringFinitePostMap
  rw [comp_lift, lift_map]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pair_eq_of_anodyneQ_eq
  · apply congrArg AnodyneHomotopy.anodyneQ.map
    rw [← Functor.map_comp, ← Functor.map_comp, weakStringVertexTopExact_postcomp]
  · apply finProduct_eq_of_anodyneQ_eq
    intro i
    simpa only [weakStringConsecutiveCofibers, Category.assoc, Limits.Pi.map_π,
      Pi.lift_comp_π_assoc, Pi.lift_comp_π, Functor.map_comp] using
      weakStringCofiberMultiMap_postcomp f q (consecutiveWeakStringEdge n i) r

end SerrePositivity.KST.Fibration
