module
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalBFComparison
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFFirstRowSimplices

/-!
概要：同じ無条件実 I・P・Z の反復に、全四角形同型と標準単体商比較を代入する。
方針：各段の同じ実商で一回の S• fibration を得て、元の連結比較へ渡す。
規約：F1 由来の全四角形比較・Sp 有限図式比較・共終性は明示定理引数。
使われ方：K-6 c4・c5 の二供給から K-7 d3 の実連結比較への対象別接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
local instance unconditionalFirstRowSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hIso : ∀ n : ℕ,
    let D := dgSuspensionUnconditionalIteration R κ hκ A n
    let I := (dgSuspensionIterationStage R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone
    let d := dgKappaNativeVerdierDiagram R D I
    FunctorIso (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection))
  (hrow : ∀ n m : ℕ,
    let D := dgSuspensionUnconditionalIteration R κ hκ A n
    let I := (dgSuspensionIterationStage R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone
    IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient (dgKappaNativeQuotient R D I) m)))
include hIso hrow

/-- 概要：同じ実反復の全四角形・標準単体比較から、各段の未完備全 S• 引き戻し。
方針：元の同じ実 I を二比較の受け渡しへ代入する。
規約：hIso・hrow に条件付き。独立した hS・I・P・Z の存在入力は取らない。
使われ方：K-7 c5・d3 の一回の S• fibration 条件の放電を二供給へ分離する。 -/
theorem dgSuspensionUnconditionalFirstRow_fibration :
    ∀ n : ℕ, IsPullbackSquare
      ((dgKappaNativeVerdierDiagram R (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).square ≫
            coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)) := by
  intro n
  exact dgKappaNativeFullSSquare_isPullback_of_kernelIso_firstRowSimplices R
    (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone
    (hIso n) (hrow n)

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    F2.Idempotent.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

/-- 概要：同じ二比較から、元の固定 K と同じ実非連結化候補の連結比較は非負次数 π 同型。
方針：同じ各段の一回の S• fibration を採用済みの連結比較へ代入する。
規約：hIso・hrow・hcofinal に条件付き。固定連結 K の Sp 引き戻し性は主張しない。
使われ方：K-7 d3 の実 I・P・Z を消費した対象別比較。 -/
theorem dgSuspensionUnconditionalFirstRow_connectedComparison_nonnegative
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionUnconditionalBFConnectedComparison R κ hκ A hcofinal) j) :=
  dgSuspensionUnconditionalBFConnectedComparison_nonnegative R κ hκ A hcofinal
    (dgSuspensionUnconditionalFirstRow_fibration R κ hκ A hIso hrow) j hj

/-- 概要：元の連結 SOA K から同じ実候補への比較も非負次数 π 同型。
方針：同じ各段の実未完備 S• fibration を既存の SOA 比較へ渡す。
規約：hIso・hrow・hcofinal に条件付き。全入力関手性・局所化登録は結論しない。
使われ方：K-7 d3 の元の連結 K 模型への照合。 -/
theorem dgSuspensionUnconditionalFirstRow_SOAComparison_nonnegative
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionUnconditionalBFSOAComparison R κ hκ A hcofinal) j) :=
  dgSuspensionUnconditionalBFSOAComparison_nonnegative R κ hκ A hcofinal
    (dgSuspensionUnconditionalFirstRow_fibration R κ hκ A hIso hrow) j hj

end SerrePositivity.KST.NonConnective
