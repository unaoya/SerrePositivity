module
public import SerrePositivity.KST.Fibration.WeakRelativeMultiAction
public import SerrePositivity.KST.Fibration.WeakStringFiniteFaces

/-! # 元の W 辺の終点と有限比較の第零面を核の作用として回収する -/

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

/-- 任意の元の実合成辺の終点評価は、始点と同じ共通 cofiber による核の作用である。 -/
theorem weakStringVertexMultiAction {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (weakStringVertexTopExact q n (α.toOrderHom 1))) =
        AnodyneHomotopy.anodyneQ.map (lift
          ((multiRealizationFunctor (r + 1)).map
            (weakStringVertexTopExact q n (α.toOrderHom 0)))
          (weakStringCofiberMultiMap q α (r + 1))) ≫ weakRelativeMultiAction q r := by
  have h := weakRelativeMultiAction_of_relativeFunctor q r (weakStringCofiberExact q α)
  rw [weakStringCofiberMiddle_eq, weakStringCofiberSubobject_eq] at h
  exact h

/-- 第零面の元の初期成分は、同じ初期成分と第一 cofiber 成分の核の作用である。 -/
theorem weakStringFiniteComparison_face_zero_action {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map
        (weakStringExactMap q (SimplexCategory.δ (0 : Fin (n + 2)))) ≫
        weakStringFiniteComparison q n (r + 1) ≫ fst _ _) =
      AnodyneHomotopy.anodyneQ.map (lift
        (weakStringFiniteComparison q (n + 1) (r + 1) ≫ fst _ _)
        (weakStringFiniteComparison q (n + 1) (r + 1) ≫ snd _ _ ≫ Pi.π _ 0)) ≫
          weakRelativeMultiAction q r := by
  rw [weakStringFiniteComparison_face_zero_initial, weakStringFiniteComparison_initial,
    weakStringFiniteComparison_cofiber]
  exact weakStringVertexMultiAction q (consecutiveWeakStringEdge (n + 1) 0) r

end SerrePositivity.KST.Fibration
