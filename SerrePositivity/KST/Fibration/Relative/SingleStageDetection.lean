module
public import SerrePositivity.KST.Fibration.Relative.ConnectiveInterface
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFOneStage

/-!
概要：相対実現の二比較を、K-B の同じ native 実 fiber 比較へ直接渡す。
方針：元の単回全 S• 四角形の引き戻し性を既存の第一正段検出へ適用する。
規約：未完備厳密 dg 入力と供給済み有限 BF 四角形を保持。検出証明は複製しない。
使われ方：K-6 b から d の非負次数 π 同型への公開界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.NonConnective
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative
local instance nativeRelativeCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：c の二比較から K-B の元の実 fiber 比較の非負次数 π 同型を得る。
方針：供給境界の単回実現結果を既存の native 第一段検出へ渡す。
規約：ν 像の Verdier 認証・全正反復収縮は要求しない。
使われ方：d の既存の dgKappaSuppliedBFFiberComparison をそのまま消費。 -/
theorem dgKappaRelativeFiberComparison_nonnegative
    (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
    {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
    (c : SingleRelativeComparison (dgKappaNativeVerdierDiagram R D I))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).toTruncated) j) :=
  dgKappaSuppliedBFFiberComparison_nonnegative R D I
    (c.isPullback (dgKappaNativeVerdierDiagram R D I)) j hj

/-- 概要：c4 の全図式同型と c5 の正段商比較を引数のまま d へ渡す。
方針：同じ二入力から相対実現比較を作り、元の native 比較へ適用。
規約：両入力は c の未解消部分。使われ方：K-B が構造体を作らず直接代入する入口。 -/
theorem dgKappaRelativeFiberComparison_nonnegative_of_positiveStages
    (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
    {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap (dgKappaNativeVerdierDiagram R D I).projection (n + 1))))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare (dgKappaNativeVerdierDiagram R D I).inclusion
        (dgKappaNativeVerdierDiagram R D I).projection))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).toTruncated) j) :=
  dgKappaRelativeFiberComparison_nonnegative R D I
    (SingleRelativeComparison.ofPositiveStages (dgKappaNativeVerdierDiagram R D I) hq e) j hj

end SerrePositivity.KST.Fibration.Relative
