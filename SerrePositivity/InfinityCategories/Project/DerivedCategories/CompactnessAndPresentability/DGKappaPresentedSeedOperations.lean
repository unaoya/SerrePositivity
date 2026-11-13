module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedSourceModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaClosedProjectiveOperations
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})
  (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
  (c : DGCategoryPresentationCode R κ)

def dgKappaPresentedSeedBinary
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_binary R (c.Objects R κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i j).choose

lemma dgKappaPresentedSeedBinary_value
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedBinary R κ hκ hreg c i j) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ⨿ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt dgKappaPresentedSeedBinary
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_binary R (c.Objects R κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i j).choose_spec

def dgKappaPresentedSeedCountable
    (i : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_countable R (c.Objects R κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i).choose

lemma dgKappaPresentedSeedCountable_value
    (i : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedCountable R κ hκ hreg c i) =
      ∐ (fun n => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c (i n)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt dgKappaPresentedSeedCountable
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_countable R (c.Objects R κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i).choose_spec

def dgKappaPresentedSeedCone
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt at f
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_cone R (c.Objects R κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i j f).choose

lemma dgKappaPresentedSeedCone_value
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedCone R κ hκ hreg c i j f) =
      moduleCone R (c.Objects R κ) f := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt at f ⊢
  unfold dgKappaPresentedSeedCone
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_cone R (c.Objects R κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i j f).choose_spec

end SerrePositivity.InfinityCategories.Project.DerivedCategories
