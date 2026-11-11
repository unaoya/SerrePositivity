module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFFixedStructure
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeFibrationTail

/-!
概要：一回の S• 比較と実供給 BF 四角形からの実構造辺で、元の反復列と実非連結化候補へ接続する。
方針：各段の同じ実 cone・実商の loop 比較を既存の実逐次余錐へ代入する。
規約：共終性・一回の未完備 S• fibration に条件付き。任意の fibration 辺は仮定しない。
使われ方：K-7 c5・d3 の実 S3 と二頂点同型を消費する利用側。
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
local instance suppliedBFSequenceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : ∀ n : ℕ, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)

/-- 概要：各段の実供給 BF 四角形から得た元の未完備実 fibration 辺。
方針：同じ段の同じ実 cone と同じ全 S• 比較を代入する。
規約：供給命題等に条件付きで、別の fibration 辺の存在は仮定しない。
使われ方：元の固定 K 構造辺を反復する実入力。 -/
def dgSuspensionSuppliedBFFibrationEdge (n : ℕ) :=
  dgKappaSuppliedBFOldFibrationEdge R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone hcofinal (Z n)

/-- 概要：各段の元の固定 K の間の実構造辺。
方針：同じ未完備実 fibration 辺を元の P・Yoneda 比較に代入する。
規約：固定 S・ν・K と元の反復を保持する。
使われ方：K-7 c5 の同じ native loop 逐次列。 -/
def dgSuspensionSuppliedBFStructureEdge :=
  dgSuspensionNativeFibrationStructureEdge R s A
    (dgSuspensionSuppliedBFFibrationEdge R s A hcofinal Z)

/-- 概要：実供給 BF 四角形からの構造辺を持つ実非連結化候補。
方針：元の実逐次 BF 列の同じ実 Sp 余極限を使う。
規約：段別供給等に条件付き。全入力自然性・局所化登録は主張しない。
使われ方：K-7 c5 の利用側。 -/
def dgSuspensionSuppliedBFCandidate :=
  dgSuspensionNativeCandidate R s A (dgSuspensionSuppliedBFStructureEdge R s A hcofinal Z)

/-- 概要：同じ候補を頂点とする元の実 Sp 余極限余錐。
方針：同じ全一単体を持つ実逐次列の余錐を回収する。
規約：群の余極限のみではなく元の Sp 図式を保持する。
使われ方：K-7 c5 の実非連結化候補への接続。 -/
def dgSuspensionSuppliedBFCandidateCocone :=
  dgSuspensionNativeCandidateCocone R s A
    (dgSuspensionSuppliedBFStructureEdge R s A hcofinal Z)

/-- 概要：同じ候補の元の実 Sp 余錐は全写像空間で余極限。
方針：既存の実余錐の極限性を同じ構造辺へ適用する。
規約：共終性・一回の未完備 S• fibration に条件付き。
使われ方：K-7 c5 の実余極限性。 -/
theorem dgSuspensionSuppliedBFCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionSuppliedBFCandidateCocone R s A hcofinal Z) :=
  dgSuspensionNativeCandidateCocone_isColimit R s A _

/-- 概要：元の連結固定 K から同じ実候補への実比較射。
方針：同じ実 Sp 余錐の零段の元の脚を使う。
規約：比較の始点と同じ候補を保持する。
使われ方：K-7 d3 の連結比較。 -/
def dgSuspensionSuppliedBFConnectedComparison :=
  dgSuspensionConnectedComparison R s A
    (dgSuspensionSuppliedBFStructureEdge R s A hcofinal Z)

variable (hS : ∀ n : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
  ((dgKappaNativeVerdierDiagram R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))

include hS in
/-- 概要：実供給 BF 四角形からの連結比較は非負次数 π 同型。
方針：同じ実 loop 比較と完備化を経る元の隣接安定化を使う。
規約：段別供給等に条件付き。固定 K の Sp 引き戻し性は仮定しない。
使われ方：K-7 d3 の元の連結 K と同じ実候補の比較。 -/
theorem dgSuspensionSuppliedBFConnectedComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionSuppliedBFConnectedComparison R s A hcofinal Z) j) :=
  dgSuspensionNativeFibrationConnectedComparison_bijective R s A _ hcofinal
    (fun n k hk => dgKappaSuppliedBFOldFibrationEdge_nonnegative R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone hcofinal (Z n) (hS n) k hk) j hj

/-- 概要：同じ実候補の任意整数 π を、十分後の元の懸垂 K 群から比較する。
方針：同じ実 fibration 辺による既存の末尾表示へ代入する。
規約：段別供給等に条件付き。候補の負群消滅は主張しない。
使われ方：K-7 d3 の同じ実候補の全整数群の記述。 -/
def dgSuspensionSuppliedBFCandidate_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionSuppliedBFCandidate R s A hcofinal Z) j :=
  dgSuspensionNativeFibrationCandidate_tailPiEquiv R s A _ hcofinal
    (fun m k hk => dgKappaSuppliedBFOldFibrationEdge_nonnegative R (dgSuspensionIteration R s A m)
      (dgSuspensionIterationStage R s A m).cone hcofinal (Z m) (hS m) k hk) j n hn

/-- 概要：同じ連結 SOA K から元の実候補への実比較射。
方針：元の固定 K への同じ実 SOA 比較に、同じ実余錐の零段の脚を続ける。
規約：段別二頂点比較 と共終性に条件付き。別の候補や固定 K を選ばない。
使われ方：K-7 d3 の元の連結 K との照合。 -/
def dgSuspensionSuppliedBFSOAComparison :=
  dgSuspensionSOAConnectedComparison R s A
    (dgSuspensionSuppliedBFStructureEdge R s A hcofinal Z)

include hS in
/-- 概要：同じ連結 SOA K からの実比較も、一回の S• fibration に条件付きで非負次数 π 同型。
方針：元の実 SOA 比較の π 同型と同じ実余錐への連結比較を合成する。
規約：全段の Sp 引き戻し性や K₀ 全射性は仮定しない。
使われ方：K-7 d3 の連結比較の採用済み主経路。 -/
theorem dgSuspensionSuppliedBFSOAComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionSuppliedBFSOAComparison R s A hcofinal Z) j) := by
  rw [dgSuspensionSuppliedBFSOAComparison, dgSuspensionSOAConnectedComparison,
    OmegaSpectrum.homotopyMap_comp]
  exact (dgSuspensionSuppliedBFConnectedComparison_nonnegative
    R s A hcofinal Z hS j hj).comp
    (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R A j)

set_option maxRecDepth 4096 in
-- 同じ実構造辺を含む反復末尾表示の依存型の照合に限って深さを増やす。
/-- 概要：同じ段別 π 表示は元の隣接構造射を通っても同じ実余錐の脚となる。
方針：同じ実 fibration 辺を既存の末尾表示の自然性へ代入する。
規約：一回の S• 比較に条件付き。負群の消滅は主張しない。
使われ方：K-7 d3 の同じ実候補の全整数群表示の整合。 -/
theorem dgSuspensionSuppliedBFCandidate_tailPiEquiv_succ
    (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n)
    (x : OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n)) :
    dgSuspensionSuppliedBFCandidate_tailPiEquiv R s A hcofinal Z hS j (n + 1)
        (Nat.le_succ_of_le hn)
        (dgSuspensionShiftedTransition R s A
          (dgSuspensionSuppliedBFStructureEdge R s A hcofinal Z) n j x) =
      dgSuspensionSuppliedBFCandidate_tailPiEquiv R s A hcofinal Z hS j n hn x :=
  dgSuspensionNativeFibrationCandidate_tailPiEquiv_succ R s A _ hcofinal
    (fun m k hk => dgKappaSuppliedBFOldFibrationEdge_nonnegative R (dgSuspensionIteration R s A m)
      (dgSuspensionIterationStage R s A m).cone hcofinal (Z m) (hS m) k hk) j n hn x

end SerrePositivity.KST.NonConnective
