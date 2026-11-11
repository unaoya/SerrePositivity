module
public import SerrePositivity.KST.Fibration.VerdierLowerLongHomTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleNativeReadout

/-!
概要：元の下側全変形の長 Hom 全族を実供給から読み、指定上側合成端へ接続する。
方針：元の二短辺を Ind-S の読出しへ代入し、指定両端の実合成端輸送を使う。
規約：(9) の厳密切断・正規化対角の存在は仮定せず、読出しだけを消費する。
使われ方：K-6 c4 の実上側入力と、残る有限端点・全対角照合の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：同じ実下側全変形から、全入力点の元の native Hom を保持する長 Hom 族が得られる。
方針：元の全固定ホーンから二短辺を回収し、実供給の native 読出しを適用する。
規約：元の二短辺と実合成端を全パラメータで保持し、正規化の存在は仮定しない。
使われ方：指定上側合成端へ移す実下側入力。 -/
theorem verdierLowerNativeReadout_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
    ∃ L : (Δ[1] : SSet.{u + 1}) ⟶
        (ihom Pu).obj (verdierLowerNativeLongHomTarget d),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1] ∧
      ∀ k : (Δ[1] : SSet.{u + 1}) _⦋0⦌,
        HEq (L.app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)).map
              ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have hf := (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u + 1})) ≫=
    verdierFullSLowerDeformation_horn d
  have hg := (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u + 1})) ≫=
    verdierFullSLowerDeformation_horn d
  have hf' := verdierLowerReconstructionHorn_first d (Δ[1] : SSet.{u + 1})
  have hg' := verdierLowerReconstructionHorn_last d (Δ[1] : SSet.{u + 1})
  simp only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] at hf hg
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamily_exists_native_readout
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionFirstFamily d Δ[1])
    (verdierLowerReconstructionLastFamily d Δ[1])
    (verdierFullSLowerDeformation d).h (hf.trans hf') (hg.trans hg')

/-- 概要：元の実下側読出しから、直接端を全族で保持する指定上側合成端入力が得られる。
方針：実供給の読出しを指定両端へ戻し、同じ元の合成端比較を続ける。
規約：新しい存在仮定を取らない。指定上側二胞体の有限端点回収は別の照合とする。
使われ方：K-6 c4 の上側再構成へ渡す全長 Hom 入力。 -/
theorem verdierLowerNativeReadout_upperInput_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
    ∃ (L : (Δ[1] : SSet.{u + 1}) ⟶
        (ihom Pu).obj (verdierLowerNativeLongHomTarget d))
      (U : (Δ[1] : SSet.{u + 1}) ⟶ (ihom Pu).obj (verdierNativeLongHomTarget d)),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1] ∧
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 0) ∧
      verdierNativeLongHomStart d Δ[1] U =
        verdierNativeLongHomStart d Δ[1] (verdierLowerNativeLongHomTransport d Δ[1] L) := by
  obtain ⟨L, hL, _⟩ := verdierLowerNativeReadout_exists d
  let q := verdierLowerNativeLongHomTransport d Δ[1] L
  have hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 1) :=
    verdierLowerNativeLongHomTransport_full d Δ[1] L hL
  exact ⟨L, verdierNativeLongHomShiftFamily d Δ[1] q hq, hL,
    verdierNativeLongHomShiftFamily_full d Δ[1] q hq,
    verdierNativeLongHomShiftFamily_start d Δ[1] q hq⟩

end SerrePositivity.KST.Fibration
