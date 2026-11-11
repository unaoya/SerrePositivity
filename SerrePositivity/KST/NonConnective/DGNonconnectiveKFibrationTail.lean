module
public import SerrePositivity.KST.NonConnective.DGNonconnectiveKConnectiveComparison
public import SerrePositivity.KST.Fibration.Relative.ConnectiveFibration

/-!
概要：K-6 の同じ実 BF fiber 比較を、各実懸垂段と非連結 K の全整数末尾表示へ渡す。
方針：無条件 k6Fibration の d を元の全反復へ代入し、固定 K の復号比較と実余錐の脚で移す。
規約：hc5 の追加入力なし。元の BF 商射と fiber を保持し、非連結化後の Verdier fiber 性は別工程。
使われ方：K-7 e の連結版 fibration 入力の消費。全入力作用や Sp 安定性は要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Fibration SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
local instance ncKFibrationCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 各段の同じ I から得た、元の実 fiber・商射・非負次数比較。 -/
theorem dgNonconnectiveKFibrationConclusions (n : ℕ) :
    Relative.K6FibrationConclusions R (dgSuspensionUnconditionalIteration R κ hκ A n)
      (dgSuspensionIterationStage R
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone :=
  Relative.k6Fibration R _ _

/-- 元の実 BF 極限錐の頂点そのものを復号した、各段の同じ実 fiber 対象。 -/
def dgNonconnectiveKFibrationFiber (n : ℕ) : OmegaSpectrum.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (dgKappaSuppliedBFKLimitCone R
    (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionIterationStage R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).vertex

/-- 同じ段の実 fiber の右辺は、元の指定 BF 商射の全一単体と厳密一致する。 -/
theorem dgNonconnectiveKFibration_quotientEdge (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaSuppliedBFCanonicalFiberSquare R
      (dgSuspensionUnconditionalIteration R κ hκ A n)
      (dgSuspensionIterationStage R
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow R
        (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone 1).hom).edge :=
  (dgNonconnectiveKFibrationConclusions R κ hκ A n).quotient_edge

/-- 同じ固定 K の復号比較を通る、K-6 d の元の実 fiber 比較の非負次数同型。 -/
def dgNonconnectiveKFibrationStagePiEquiv (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    OmegaSpectrum.homotopyGroup (dgNonconnectiveKSuspensionK R κ hκ A n) k ≃*
      OmegaSpectrum.homotopyGroup (dgNonconnectiveKFibrationFiber R κ hκ A n) k := by
  let K := dgNonconnectiveKSuspensionK R κ hκ A n
  let a := (SpectrumHo.piComparison K k).inv
  let e₁ := MulEquiv.ofBijective a.hom (ConcreteCategory.bijective_of_isIso a)
  let b := SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
    (Relative.dgKappaCanonicalFixedSourceFiberComparison R
      (dgSuspensionUnconditionalIteration R κ hκ A n)
      (dgSuspensionIterationStage R
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).toTruncated) k
  exact e₁.trans (MulEquiv.ofBijective b
    ((dgNonconnectiveKFibrationConclusions R κ hκ A n).fiber_nonnegative k hk))

/-- 元の固定 K と同じ実 fiber の復号 BF 対象の間で、K-6 d の実辺を表す BF 射。 -/
def dgNonconnectiveKFibrationStageMap (n : ℕ) :
    dgNonconnectiveKSuspensionK R κ hκ A n ⟶ dgNonconnectiveKFibrationFiber R κ hκ A n :=
  (SpectrumHo.spectrumIsoBF (dgNonconnectiveKSuspensionK R κ hκ A n)).inv ≫
    SpectrumHo.representative (SpectrumHo.normalize (Truncated.HomotopyCategory.homMk
      (Relative.dgKappaCanonicalFixedSourceFiberComparison R
        (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).toTruncated))

/-- 段別群同型の順方向は、元の K-6 d の辺を表す同じ BF 射の π 作用そのもの。 -/
theorem dgNonconnectiveKFibrationStageMap_pi (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    OmegaSpectrum.homotopyMap (dgNonconnectiveKFibrationStageMap R κ hκ A n) k =
      (dgNonconnectiveKFibrationStagePiEquiv R κ hκ A n k hk).toMonoidHom := by
  rw [dgNonconnectiveKFibrationStageMap, OmegaSpectrum.homotopyMap_comp]
  rfl

/-- 同じ実 fiber 比較を表す BF 射は非負次数 π 同型。 -/
theorem dgNonconnectiveKFibrationStageMap_nonnegative (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgNonconnectiveKFibrationStageMap R κ hκ A n) k) := by
  rw [dgNonconnectiveKFibrationStageMap_pi R κ hκ A n k hk]
  exact (dgNonconnectiveKFibrationStagePiEquiv R κ hκ A n k hk).bijective

/-- 概要：同じ非連結 K の整数 π を、十分後の同じ実 BF fiber の移動次数 π で表す。
方針：元の実余錐の末尾比較・固定 K の復号同型・K-6 d の同じ比較射を順に合成する。
規約：c5 の追加入力なし。fiber の遷移射やその逐次余極限性を新たに仮定・結論しない。
使われ方：e の非連結化後の fiber 比較へ渡す、元の実 fibration の末尾座標。
-/
def dgNonconnectiveKFibration_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup (dgNonconnectiveK R κ hκ A) j ≃*
      OmegaSpectrum.homotopyGroup (dgNonconnectiveKFibrationFiber R κ hκ A n) (j + n) :=
  (dgNonconnectiveK_tailPiEquiv R κ hκ A j n hn).symm.trans
    (dgNonconnectiveKFibrationStagePiEquiv R κ hκ A n (j + n) (by
      have hb := Int.self_le_toNat (-j)
      omega))

/-- 末尾 fiber 座標は元の実余錐の脚を通ると、同じ段の K-6 d の比較を回収する。 -/
theorem dgNonconnectiveKFibration_tailPiEquiv_injection
    (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) (hj : 0 ≤ j + (n : ℤ))
    (x : OmegaSpectrum.homotopyGroup (dgNonconnectiveKStage R κ hκ A n) j) :
    dgNonconnectiveKFibration_tailPiEquiv R κ hκ A j n hn
        (OmegaSpectrum.homotopyMap (dgNonconnectiveKInjection R κ hκ A n) j x) =
      dgNonconnectiveKFibrationStagePiEquiv R κ hκ A n (j + n) hj
        (dgNonconnectiveKStage_piEquiv R κ hκ A n j x) := by
  have hx : OmegaSpectrum.homotopyMap (dgNonconnectiveKInjection R κ hκ A n) j x =
      dgNonconnectiveK_tailPiEquiv R κ hκ A j n hn
        (dgNonconnectiveKStage_piEquiv R κ hκ A n j x) := by
    simp only [dgNonconnectiveK_tailPiEquiv, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply]
  rw [hx]
  exact congrArg (dgNonconnectiveKFibrationStagePiEquiv R κ hκ A n (j + n) hj)
    ((dgNonconnectiveK_tailPiEquiv R κ hκ A j n hn).symm_apply_apply _)

end SerrePositivity.KST.NonConnective
