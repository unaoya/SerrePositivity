module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaOrdinalCountableBound

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
lemma dgKappaClosedProjectiveObjects_countableClosed {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    (M : ℕ → ModuleCategory R D) (hM : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (M n)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (∐ M) := by
  choose i hi using hM
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_countable R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i
  refine ⟨j, hj.trans ?_⟩
  exact congrArg (fun N : ℕ → ModuleCategory R D ↦ ∐ N) (funext hi)

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_binaryClosed {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    (M N : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M)
    (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (M ⨿ N) := by
  obtain ⟨i, rfl⟩ := hM
  obtain ⟨j, rfl⟩ := hN
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_binary R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i j

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_zero {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (moduleZero R D) := by
  have : Nonempty κ.ord.ToType := by
    exact Cardinal.nonempty_ord_toType (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_zero R D _

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_shift {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    (M : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (M⟦s⟧) := by
  obtain ⟨i, rfl⟩ := hM
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_shift R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ s i

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_cone {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    (M N : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M)
    (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N) (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (moduleCone R D f) := by
  obtain ⟨i, rfl⟩ := hM
  obtain ⟨j, rfl⟩ := hN
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_cone R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg) _ i j f

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_sphereFree {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i) := by
  have : Nonempty κ.ord.ToType :=
    Cardinal.nonempty_ord_toType (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_base R D (T := κ.ord.ToType)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ) (.inl i)
  exact ⟨j, congrArg Subtype.val hj⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
