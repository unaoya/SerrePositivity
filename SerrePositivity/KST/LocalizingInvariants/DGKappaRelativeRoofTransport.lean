module

public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagramComparison
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullSquare
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionRelativeRoofInput

/-!
概要：実 ν 像の認証と指定境界の比較を、K-B の既存の相対屋根型へ接続する。
方針：元の三頂点と実商の全一単体を保持し、ofSquare の認証をそのまま渡す。
規約：I・P・既存の屋根型は変更せず、実核・Verdier 証拠・Perf 零性の存在を仮定済み成果にしない。
使われ方：Sp-6 の固定 ν 上の相対懸垂接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.LocalizingInvariants

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 指定された三境界の全 ν 比較を持つ実相対屋根。全フィールドは未供給入力。 -/
structure DGKappaRelativeRoofComparisonInput where
  kernel : PerfDGInput.{u, max (u + 1) v} R
  diagram : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, max (u + 1) v} R)
  target : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{max (u + 1) v}
  boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (diagram.square ≫ dgKInputNu R) target.square
  image : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (diagram.square ≫ dgKInputNu R) target.square boundary
  left_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex diagram.square 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex kernel
  middle_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex diagram.square 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaResolvedConeKInput R D I)
  right_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex diagram.square 1 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R D I)
  quotient : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ diagram.square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedSuspensionInputMap R D I)).edge

namespace DGKappaRelativeRoofComparisonInput
variable {R D I} (t : DGKappaRelativeRoofComparisonInput R D I)

/-- K-B の既存の厳密な三頂点・商辺を持つ型へ、同じ実図式を渡す。 -/
def toStrict : DGKappaSuspensionRelativeRoofInput R D I where
  kernel := t.kernel
  diagram := t.diagram
  left_eq := t.left_eq
  middle_eq := t.middle_eq
  right_eq := t.right_eq
  quotient := t.quotient

@[simp] lemma toStrict_diagram : t.toStrict.diagram = t.diagram := rfl

/-- 同じ相対不変量の fiber 性は、既存の厳密屋根の同じ図式へ輸送される。 -/
theorem toStrict_isPullback {E : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    Spectra.Sp.{max (u + 1) v}} (hE : IsRelativeLocalizingInvariant (dgKInputNu R) E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (t.toStrict.diagram.square ≫ E) := hE.preservesVerdier t.diagram

end DGKappaRelativeRoofComparisonInput

/-- 実核・指定収縮・元の二射の Verdier 証拠・Perf 零性が届いた場合の、厳密屋根の実供給。
ν の全図式比較は存在の前提に追加せず、実像の ofSquare 認証だけを用いる。 -/
lemma exists_dgKappaRelativeRoof_of_fixedNull
    (A : PerfDGInput.{u, max (u + 1) v} R)
    (i : A ⟶ dgKappaResolvedConeKInput R D I)
    (C : DGQuotient.ContractedFunctor R A Set.univ (dgKappaSuspensionKInput R D I))
    (hC : C.toDGFunctor = i.down.comp (dgKappaResolvedSuspensionInputMap R D I).down)
    (hV : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKInputNuMap R i)
      (dgKInputNuMap R (dgKappaResolvedSuspensionInputMap R D I)))
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R A))) :
    ∃ t : DGKappaSuspensionRelativeRoofInput R D I, t.kernel = A ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.diagram.square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge := by
  obtain ⟨t, ha, hb, hq, hi, hr⟩ := exists_dgFixedNullRelativeRoof R i
    (dgKappaResolvedSuspensionInputMap R D I) C hC hV hz
  exact ⟨⟨A, t, ha, hb, hq, hr⟩, rfl, hi⟩

end SerrePositivity.KST.LocalizingInvariants
