module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedBarVertexComparison
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
概要：実導来 bar 像の native 余極限性から、正本の strict 比較述語を構成する。
方針：同じ図式の実余錐と、C1 から得た strict 余極限頂点への同型を合わせる。
規約：全加群 dg nerve における B の余極限性と、その実導来像の余極限性を区別する。
使われ方：実導来像への移送定理の消費側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

def dgKappaStrictFilteredColimitComparison_of_barImageIsColimit
    (himage : ∀ (J : Type u) [PartialOrder J] [IsCardinalFiltered J κ]
      (F : J ⥤ ModuleCategory R D), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictDerivedBarCocone R D F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaStrictFilteredColimitComparison R D κ := by
  intro J _ _ F c hc
  letI := isFiltered_of_isCardinalFiltered J κ
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictDerivedBarCocone R D F, himage J F,
    ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictDerivedBarCocone_vertexIso R D F c hc⟩⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
