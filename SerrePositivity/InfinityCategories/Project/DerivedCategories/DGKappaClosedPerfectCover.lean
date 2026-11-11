module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveOperations

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

/-- 小さい実射影的 perfect 代表と、同じ導来圏での被覆。 -/
lemma dgKappaClosedProjectiveObjects_perfectRepresentative {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ)
    (i : SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i) := by
  have : Nonempty κ.ord.ToType :=
    Cardinal.nonempty_ord_toType (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_base R D (T := κ.ord.ToType)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ) (.inr i)
  exact ⟨j, congrArg Subtype.val hj⟩

/-- 小さい実射影的 perfect 代表と、同じ導来圏での被覆。 -/
lemma dgKappaClosedProjectiveObjects_perfectCovers {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (M : ModuleCategory R D)
    (hM : modulePerfect R D ((moduleToDerived R D).obj M)) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty ((moduleToDerived R D).obj N ≅ (moduleToDerived R D).obj M) := by
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative_covers R D M hM
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i,
    dgKappaClosedProjectiveObjects_perfectRepresentative R D hκ i, hi⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
