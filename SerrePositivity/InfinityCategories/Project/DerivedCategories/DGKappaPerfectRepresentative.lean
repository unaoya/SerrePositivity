module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

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
def dgKappaPerfectRepresentative
    (i : SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)) : ModuleCategory R D :=
  ForgetEnrichment.of (Complex R) (perfectDGModuleRepresentative R D Set.univ i).val

/-- 小さい実射影的 perfect 代表と、同じ導来圏での被覆。 -/
lemma dgKappaPerfectRepresentative_projective
    (i : SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)) :
    moduleHomotopicallyProjective R D (dgKappaPerfectRepresentative R D i) :=
  (perfectDGModuleRepresentative R D Set.univ i).property.1

/-- 小さい実射影的 perfect 代表と、同じ導来圏での被覆。 -/
lemma dgKappaPerfectRepresentative_covers (M : ModuleCategory R D)
    (hM : modulePerfect R D ((moduleToDerived R D).obj M)) :
    ∃ i : SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ),
      Nonempty ((moduleToDerived R D).obj (dgKappaPerfectRepresentative R D i) ≅
        (moduleToDerived R D).obj M) := by
  let X : PerfectModuleCategoryOver R D Set.univ := ⟨(moduleToDerived R D).obj M, hM⟩
  let e := equivSmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)
  let i := e.functor.obj X
  let Y := (perfectDGModuleHomotopyEquivalence R D Set.univ).inverse.obj (e.inverse.obj i)
  let q := (perfectDGModuleHomotopyEquivalence R D Set.univ).counitIso.app
    (e.inverse.obj i) ≪≫ (e.unitIso.app X).symm
  refine ⟨i, ⟨?_⟩⟩
  exact ((moduleToHomotopyDerivedIso R D).app (dgKappaPerfectRepresentative R D i)).symm ≪≫
    (modulePerfectOver R D Set.univ).ι.mapIso q

end SerrePositivity.InfinityCategories.Project.DerivedCategories
