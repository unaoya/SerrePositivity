module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagramComparison

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierPresentation
public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierPullback

/-!
概要：相対 Verdier 図式の全比較を、包含・商・零角の指定比較に固定する。
方針：境界比較を先に指定し、全図式同型の制限との一致を型に含める。
規約：ν 像の同型から S 内の厳密代表の存在を推論しない。
使われ方：K-S• の長方形と K-B の相対懸垂屋根の比較接続口。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

namespace RelativeVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}

/-- 厳密な代表が別途供給された場合、同じ E の値の pullback を全源図式同型で輸送する。 -/
lemma comparison_isPullback_of_sourceIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle ν)
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso d.diagram F)
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso d.diagram F b)
    {E : S ⟶ Spectra.Sp.{u}} (hE : IsRelativeLocalizingInvariant ν E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ E) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact ((_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonSquare_isPullback d) hE).of_functorIso
    ((e.comparison.precomp c).postcomp E)

end RelativeVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants
