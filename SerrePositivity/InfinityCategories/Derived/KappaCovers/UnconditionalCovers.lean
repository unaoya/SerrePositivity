module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedStrictFilteredComparison
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.Covers

/-!
概要：正則非可算 κ の全 compact 頂点を実代表系で被覆する。
方針：coherent bar の C1・B 比較から構成した native/strict 比較を代入する。
規約：余極限比較を追加の仮定には残さない。
使われ方：DGKappaConeInput.covers の D 側の無条件供給。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial

lemma dgKappaCone_covers_unconditional
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (hy : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (VertexIso (dgConeModuleDerivedVertex R D N) y) :=
  dgKappaCone_covers_of_strictFilteredColimitComparison R D κ hκ
    (dgKappaStrictFilteredColimitComparison_unconditional R D κ) y hy

end SerrePositivity.InfinityCategories
