module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceModel
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectiveOperations
/-!
概要：共通出発提示の seed の二項・可算直和と任意閉射の cone を保持する。
方針：既存の実射影的閉包が供給する添字と実加群の等式をそのまま使用する。
規約：選択は code と seed と元の閉射だけに依存し、標的 arrow を参照しない。
使われ方：同時精密化で共通提示へ戻した後の実閉演算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})
  (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
  (c : DGCategoryPresentationCode R κ)

def dgKappaPresentedSeedBinary
    (i j : (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 :=
  (dgProjectiveClosureFamily_binary R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ i j).choose

lemma dgKappaPresentedSeedBinary_value
    (i j : (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedBinary R κ hκ hreg c i j) =
      (dgKappaPresentedSeedAt R κ c i ⨿ dgKappaPresentedSeedAt R κ c j) := by
  unfold dgKappaPresentedSeedAt dgKappaPresentedSeedBinary
  exact (dgProjectiveClosureFamily_binary R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ i j).choose_spec

def dgKappaPresentedSeedCountable
    (i : ℕ → (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 :=
  (dgProjectiveClosureFamily_countable R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ i).choose

lemma dgKappaPresentedSeedCountable_value
    (i : ℕ → (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedCountable R κ hκ hreg c i) =
      ∐ (fun n => dgKappaPresentedSeedAt R κ c (i n)) := by
  unfold dgKappaPresentedSeedAt dgKappaPresentedSeedCountable
  exact (dgProjectiveClosureFamily_countable R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ i).choose_spec

def dgKappaPresentedSeedCone
    (i j : (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : dgKappaPresentedSeedAt R κ c i ⟶ dgKappaPresentedSeedAt R κ c j) :
    (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 := by
  unfold dgKappaPresentedSeedAt at f
  exact (dgProjectiveClosureFamily_cone R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ i j f).choose

lemma dgKappaPresentedSeedCone_value
    (i j : (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : dgKappaPresentedSeedAt R κ c i ⟶ dgKappaPresentedSeedAt R κ c j) :
    dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedCone R κ hκ hreg c i j f) =
      moduleCone R (c.Objects R κ) f := by
  unfold dgKappaPresentedSeedAt at f ⊢
  unfold dgKappaPresentedSeedCone
  exact (dgProjectiveClosureFamily_cone R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ i j f).choose_spec

end SerrePositivity.InfinityCategories
