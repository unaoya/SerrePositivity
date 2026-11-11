module
public import SerrePositivity.KST.Fibration.ZeroMiddleLongFamilyComparison
public import SerrePositivity.KST.Fibration.CoherentTriangleIntervalEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleCoherentEncoderNative

/-!
概要：Ind-S (9) の実 canonical encoder を元の全 S• 二短辺へ直接代入する。
方針：公開された実写像と全対角・native Hom 回収を同じ入力で消費する。
規約：encode/read の厳密切断は使わず、元の任意二胞体への対角式も要求しない。
使われ方：K-6 c4 の同じ実長 Hom 入力から全共有対角を回収する。
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
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：元の全 S• 二短辺を保つ実 canonical encoder。
方針：同じ core 始域・全 S• 中間対象・core 終域を F1 正本へ代入する。
規約：供給命題の仮定は不要。read の厳密切断を主張しない。
使われ方：指定された同じ長 Hom 入力の実上側二胞体への像。 -/
def zeroMiddleCanonicalEncode :
    zeroMiddleFullSReconstructionLongSpace s hZ K ⟶
      zeroMiddleFullSReconstructionTriangleSpace s hZ K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
    (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K)
    (zeroMiddleFullSReconstructionHorn s hZ K)
    (zeroMiddleFullSReconstructionHorn_first s hZ K)
    (zeroMiddleFullSReconstructionHorn_last s hZ K)

variable (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌)

/-- 概要：同じ指定長 Hom から得る実全二胞体族。
方針：実 canonical encoder の像の同じ関手頂点を実写像へ戻す。
規約：入力の全パラメータを保持する。
使われ方：指定共有対角と native Hom を持つ実上側族。 -/
def zeroMiddleCanonicalFamily : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue
    ((zeroMiddleCanonicalEncode s hZ K).app (Opposite.op ⦋0⦌) ℓ)

/-- 概要：同じ実 canonical 族は元の二短辺の全ホーンを厳密に保持する。
方針：同じ固定ホーン fiber の像の回収式を使う。
規約：元の指定短辺を選び直さない。
使われ方：共有対角と同時に二短辺を回収する。 -/
theorem zeroMiddleCanonicalFamily_horn :
    ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ zeroMiddleCanonicalFamily s hZ K ℓ =
      zeroMiddleFullSReconstructionHorn s hZ K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue_horn _

/-- 概要：同じ canonical 像の対角は元入力の直接 path 全族を厳密回収する。
方針：F1 の実 encoder の全対角式と所有 path の端点等号を使う。
規約：全 Δ[1] ⊗ K 上の式。encode/read の切断式を使わない。
使われ方：K-6 c4 の上下の動く共有対角を同じ入力から貼る。 -/
theorem zeroMiddleCanonicalFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ zeroMiddleCanonicalFamily s hZ K ℓ =
      (Δ[1] ◁ (zeroMiddleLongPointFamily s hZ K ℓ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_diagonal
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
    (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K)
    (zeroMiddleFullSReconstructionHorn s hZ K)
    (zeroMiddleFullSReconstructionHorn_first s hZ K)
    (zeroMiddleFullSReconstructionHorn_last s hZ K) ℓ
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso_inv_first.{u, u + 1}).symm.trans
    (coherentTriangleInterval_up_first.{u})
  rw [hp] at h
  exact h

/-- 概要：実 canonical 族の各入力点の全 native Hom は元の指定入力そのもの。
方針：同じ実 encoder の公開 native Hom 回収へ同じ点を代入する。
規約：直接端の一致だけに弱めない。切断式は使わない。
使われ方：元の指定有限端点二胞体との照合。 -/
theorem zeroMiddleCanonicalFamily_native (k : K _⦋0⦌) :
    HEq ((zeroMiddleLongPointFamily s hZ K ℓ).app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleCanonicalFamily s hZ K ℓ) k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_native
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
    (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K)
    (zeroMiddleFullSReconstructionHorn s hZ K)
    (zeroMiddleFullSReconstructionHorn_first s hZ K)
    (zeroMiddleFullSReconstructionHorn_last s hZ K) ℓ k

end SerrePositivity.KST.Fibration
