module
public import SerrePositivity.KST.LocalizingInvariants.DGKappaRelativeRoofTransport
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu
public import SerrePositivity.KST.Spectra.S3ActualFaces

/-!
概要：K-B3 の既存固定 ν 屋根へ接続し、strict 入力を Perf 版の特殊化として消費する。
方針：toStrict の同じ図式・三頂点・商辺を維持し、零角 A/A の零性は既存認証を渡す。
規約：Perf 商辺から strict Verdier 性を推論しない。実核・収縮・Verdier 証拠は明示する。
使われ方：Sp-3 から K-B3 e への公開口。I・P・固定 K は変更しない。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.S3
variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の toStrict を直接渡し、三頂点と元の商一単体を保つ。 -/
def kappaToStrict (t : DGKappaRelativeRoofComparisonInput R D I) :
    DGKappaSuspensionRelativeRoofInput R D I := t.toStrict

/-- strict 屋根は同じ四角形と恒等完備化を持つ Perf 版の特殊化。 -/
def kappaPerfectDiagram (t : DGKappaSuspensionRelativeRoofInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram (dgKInputPerfectNu.{u, max (u + 1) v} R) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStrict
    (by rw [dgKInputPerfectNu_inclusion]; exact t.diagram)

@[simp] theorem kappaPerfectDiagram_square (t : DGKappaSuspensionRelativeRoofInput R D I) :
    (kappaPerfectDiagram R D I t).square = t.diagram.square := rfl

/-- 同じ固定 ν の Perf 局所化不変量を、既存屋根の元の四角形で評価する。 -/
theorem kappaPerfect_isPullback (t : DGKappaSuspensionRelativeRoofInput R D I)
    {E : perfectStableInfinity.{max (u + 1) v} ⟶ Sp.{max (u + 1) v}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (t.diagram.square ≫ dgKInputPerfectNu R ≫ E) :=
  (kappaPerfectDiagram R D I t).isPullback (dgKInputPerfectNu R) hE

/-- 実核・指定収縮・strict Verdier 証拠から元の屋根を供給する。
零角 A/A の Perf 零性は実認証済みなので追加入力にしない。 -/
theorem exists_kappaRelativeRoof
    (A : PerfDGInput.{u, max (u + 1) v} R)
    (i : A ⟶ dgKappaResolvedConeKInput R D I)
    (C : DGQuotient.ContractedFunctor R A Set.univ (dgKappaSuspensionKInput R D I))
    (hC : C.toDGFunctor = i.down.comp (dgKappaResolvedSuspensionInputMap R D I).down)
    (hV : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKInputNuMap R i)
      (dgKInputNuMap R (dgKappaResolvedSuspensionInputMap R D I))) :
    ∃ t : DGKappaSuspensionRelativeRoofInput R D I, t.kernel = A ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.diagram.square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge :=
  exists_dgKappaRelativeRoof_of_fixedNull R D I A i C hC hV
    (dgFixedNullInput_isZeroCategory R A)

end SerrePositivity.KST.Spectra.S3
