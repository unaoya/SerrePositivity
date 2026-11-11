module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveClosureProperty

/-!
概要：正則非可算 κ の小さい射影的代表族を、実際の加群演算で閉じる。
方針：小さい超限段階と可算個の段階の狭義上界で、同じ代表族の閉性を証明する。
規約：全同型コピーを集めず、全共変 Hom の κ-compact 性は別に証明する。
使われ方：K-7 の実 dg 小模型への対象・小ささ・射影性・直和閉性の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_property {κ : Cardinal.{u}}
    (P : ModuleCategory R D → Prop)
    (hzero : P (moduleZero R D))
    (hshift : ∀ M, P M → ∀ s : ℤ, P (M⟦s⟧))
    (hbinary : ∀ M N, P M → P N → P (M ⨿ N))
    (hcone : ∀ M N, P M → P N → ∀ f : M ⟶ N, P (moduleCone R D f))
    (hcountable : ∀ M : ℕ → ModuleCategory R D, (∀ n, P (M n)) → P (∐ M))
    (hbase : ∀ i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ, P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i))
    (hperfect : ∀ i, P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i))
    (M : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) : P M := by
  obtain ⟨⟨a, i⟩, rfl⟩ := hM
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_property R D P hzero hshift hbinary hcone hcountable
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ) _ a i
  intro j
  rcases j with j | j
  · exact hbase j
  · exact hperfect j

end SerrePositivity.InfinityCategories.Project.DerivedCategories
