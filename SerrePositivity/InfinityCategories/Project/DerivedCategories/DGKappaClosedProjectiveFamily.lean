module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPerfectRepresentative
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveClosureFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeFamily

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
def dgKappaClosedProjectiveBaseFamily (κ : Cardinal.{u}) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilySum R D
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ,
      fun i ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_projective R D i⟩⟩
    ⟨SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ),
      fun i ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative_projective R D i⟩⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
def dgKappaClosedProjectiveFamily (κ : Cardinal.{u}) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := κ.ord.ToType)
    (dgKappaClosedProjectiveBaseFamily R D κ)

/-- 同じ実代表族の構成・閉性を保持する。 -/
def dgKappaClosedProjectiveObjects (κ : Cardinal.{u}) : Set (ModuleCategory R D) :=
  Set.range (fun i ↦ ((dgKappaClosedProjectiveFamily R D κ).2 i).val)

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_small (κ : Cardinal.{u}) :
    Small.{u} {M : ModuleCategory R D // dgKappaClosedProjectiveObjects R D κ M} :=
  small_range _

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgKappaClosedProjectiveObjects_projective (κ : Cardinal.{u})
    (M : ModuleCategory R D) (hM : dgKappaClosedProjectiveObjects R D κ M) :
    moduleHomotopicallyProjective R D M := by
  obtain ⟨i, rfl⟩ := hM
  exact ((dgKappaClosedProjectiveFamily R D κ).2 i).property

end SerrePositivity.InfinityCategories.Project.DerivedCategories
