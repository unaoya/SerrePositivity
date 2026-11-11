module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedStrictFilteredComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.Covers

/-!
概要：正則非可算 κ の全 compact 頂点を実代表系で被覆する。
方針：coherent bar の C1・B 比較から構成した native/strict 比較を代入する。
規約：余極限比較を追加の仮定には残さない。
使われ方：DGKappaConeInput.covers の D 側の無条件供給。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial

lemma dgKappaCone_covers_unconditional
    (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D N) y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCone_covers_of_strictFilteredColimitComparison R D κ hκ
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictFilteredColimitComparison_unconditional R D κ) y hy

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
