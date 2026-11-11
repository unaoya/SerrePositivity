module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFLoopStructure
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeFibrationTail

/-!
概要：補助経路として、同じ有限 BF 四角形からの実構造辺で、元の反復列と実非連結化候補へ接続する。
方針：各段の同じ実 cone・実商の loop 比較を既存の実逐次余錐へ代入する。
規約：段別有限 BF・共終性・未完備全 S• fibration に条件付き。任意の fibration 辺は仮定しない。
使われ方：K-7 c5・d3 の有限 BF 供給を待つ利用側。
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
namespace SerrePositivity.KST.NonConnective
local instance nativeBFSequenceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hBF : ∀ n : ℕ, dgKappaNativeBFSquareComparison R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : ∀ n : ℕ, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (hS : ∀ (n r : ℕ), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
    ((dgKappaNativeVerdierDiagram R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone).square ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r)))

/-- 概要：各段の同じ有限 BF 四角形から得た元の未完備実 fibration 辺。
方針：同じ段の同じ実 cone と同じ全 S• 比較を代入する。
規約：供給命題等に条件付きで、別の fibration 辺の存在は仮定しない。
使われ方：元の固定 K 構造辺を反復する実入力。 -/
def dgSuspensionNativeBFFibrationEdge (n : ℕ) :=
  dgKappaNativeBFFibrationEdge R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (hBF n) hcofinal (Z n) (hS n)

/-- 概要：各段の元の固定 K の間の実構造辺。
方針：同じ未完備実 fibration 辺を元の P・Yoneda 比較に代入する。
規約：固定 S・ν・K と元の反復を保持する。
使われ方：K-7 c5 の同じ native loop 逐次列。 -/
def dgSuspensionNativeBFStructureEdge :=
  dgSuspensionNativeFibrationStructureEdge R s A
    (dgSuspensionNativeBFFibrationEdge R s A hBF hcofinal Z hS)

/-- 概要：同じ有限 BF 四角形からの構造辺を持つ実非連結化候補。
方針：元の実逐次 BF 列の同じ実 Sp 余極限を使う。
規約：段別供給等に条件付き。全入力自然性・局所化登録は主張しない。
使われ方：K-7 c5 の利用側。 -/
def dgSuspensionNativeBFCandidate :=
  dgSuspensionNativeCandidate R s A (dgSuspensionNativeBFStructureEdge R s A hBF hcofinal Z hS)

/-- 概要：同じ候補を頂点とする元の実 Sp 余極限余錐。
方針：同じ全一単体を持つ実逐次列の余錐を回収する。
規約：群の余極限のみではなく元の Sp 図式を保持する。
使われ方：K-7 c5 の実非連結化候補への接続。 -/
def dgSuspensionNativeBFCandidateCocone :=
  dgSuspensionNativeCandidateCocone R s A
    (dgSuspensionNativeBFStructureEdge R s A hBF hcofinal Z hS)

/-- 概要：同じ候補の元の実 Sp 余錐は全写像空間で余極限。
方針：既存の実余錐の極限性を同じ構造辺へ適用する。
規約：段別供給・共終性・未完備全 S• fibration に条件付き。
使われ方：K-7 c5 の実余極限性。 -/
theorem dgSuspensionNativeBFCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionNativeBFCandidateCocone R s A hBF hcofinal Z hS) :=
  dgSuspensionNativeCandidateCocone_isColimit R s A _

/-- 概要：元の連結固定 K から同じ実候補への実比較射。
方針：同じ実 Sp 余錐の零段の元の脚を使う。
規約：比較の始点と同じ候補を保持する。
使われ方：K-7 d3 の連結比較。 -/
def dgSuspensionNativeBFConnectedComparison :=
  dgSuspensionConnectedComparison R s A
    (dgSuspensionNativeBFStructureEdge R s A hBF hcofinal Z hS)

/-- 概要：同じ有限 BF 四角形からの連結比較は非負次数 π 同型。
方針：同じ実 loop 比較と完備化を経る元の隣接安定化を使う。
規約：段別供給等に条件付き。固定 K の Sp 引き戻し性は仮定しない。
使われ方：K-7 d3 の元の連結 K と同じ実候補の比較。 -/
theorem dgSuspensionNativeBFConnectedComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionNativeBFConnectedComparison R s A hBF hcofinal Z hS) j) :=
  dgSuspensionNativeFibrationConnectedComparison_bijective R s A _ hcofinal
    (fun n k _ => dgKappaNativeBFFibrationEdge_pi_bijective R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone (hBF n) hcofinal (Z n) (hS n) k) j hj

/-- 概要：同じ実候補の任意整数 π を、十分後の元の懸垂 K 群から比較する。
方針：同じ実 fibration 辺による既存の末尾表示へ代入する。
規約：段別供給等に条件付き。候補の負群消滅は主張しない。
使われ方：K-7 d3 の同じ実候補の全整数群の記述。 -/
def dgSuspensionNativeBFCandidate_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionNativeBFCandidate R s A hBF hcofinal Z hS) j :=
  dgSuspensionNativeFibrationCandidate_tailPiEquiv R s A _ hcofinal
    (fun m k _ => dgKappaNativeBFFibrationEdge_pi_bijective R (dgSuspensionIteration R s A m)
      (dgSuspensionIterationStage R s A m).cone (hBF m) hcofinal (Z m) (hS m) k) j n hn

end SerrePositivity.KST.NonConnective
