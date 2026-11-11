module
public import SerrePositivity.KST.Fibration.VerdierLowerNativeReadoutHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleCoherentEncoderNative

/-!
概要：同じ実下側読出しを canonical encoder で正規化し、全 native Hom を保持する。
方針：元の下側二短辺と長 Hom fiber を F1 の実再構成へ特殊化する。
規約：厳密切断を使わず、同じ固定ホーン空間内の可逆比較を保持する。
使われ方：K-6 c4 の正規化下側の有限端点と全共有対角の同時照合。
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
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 概要：同じ実下側の合成端を固定した全長 Hom 空間。
方針：元の実三頂点で F1 の fiber を特殊化する。
規約：存在仮定を追加しない。使われ方：実読出しの入力登録。 -/
abbrev verdierLowerCanonicalLongSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionCompositeFamily d Δ[1])

/-- 概要：元の下側ホーンを保持する実 canonical encoder。
方針：同じ下側二短辺と全ホーン回収を公開構成へ渡す。
規約：別の二胞体の選択を行わない。使われ方：全族の正規化。 -/
def verdierLowerCanonicalEncode :
    verdierLowerCanonicalLongSpace d ⟶ verdierLowerReconstructionTriangleSpace d Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionFirstFamily d Δ[1])
    (verdierLowerReconstructionLastFamily d Δ[1])
    (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)
    (verdierLowerReconstructionHorn_first d Δ[1])
    (verdierLowerReconstructionHorn_last d Δ[1])

variable (ℓ : (verdierLowerCanonicalLongSpace d) _⦋0⦌)

/-- 概要：同じ実下側長 Hom 入力の正規化二胞体族。
方針：実 encoder の像を全族へ戻す。
規約：全時刻を同時に保持する。使われ方：全共有対角での貼り合わせ。 -/
def verdierLowerCanonicalFamily : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue ((verdierLowerCanonicalEncode d).app (Opposite.op ⦋0⦌) ℓ)

/-- 概要：正規化下側族は元の実下側ホーン全体を厳密回収する。
方針：同じホーン fiber の値を取る。
規約：二短辺の全族を固定する。使われ方：元の下側との固定ホーン内比較。 -/
theorem verdierLowerCanonicalFamily_horn :
    ((horn 2 (1 : Fin 3)).ι ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierLowerCanonicalFamily d ℓ =
      fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue_horn _

/-- 概要：正規化下側の各時刻は同じ実入力の全 native Hom を回収する。
方針：実 canonical encoder の公開 native 回収を使う。
規約：直接端だけの比較へ弱めない。使われ方：指定有限端点の照合。 -/
theorem verdierLowerCanonicalFamily_native (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue ℓ).app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_native
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionFirstFamily d Δ[1])
    (verdierLowerReconstructionLastFamily d Δ[1])
    (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)
    (verdierLowerReconstructionHorn_first d Δ[1])
    (verdierLowerReconstructionHorn_last d Δ[1]) ℓ k

/-- 概要：正規化した下側の全対角は同じ実長 Hom の直接端全族。
方針：同じ実 encoder の全対角回収を元の三頂点へ特殊化する。
規約：元の未正規化族自身への厳密回収は主張しない。
使われ方：同じ実読出しを使う上側との全共有対角の貼り合わせ。 -/
theorem verdierLowerCanonicalFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierLowerCanonicalFamily d ℓ =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue ℓ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDirectPath.{u})))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_diagonal
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionFirstFamily d Δ[1])
    (verdierLowerReconstructionLastFamily d Δ[1])
    (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)
    (verdierLowerReconstructionHorn_first d Δ[1])
    (verdierLowerReconstructionHorn_last d Δ[1]) ℓ

/-- 概要：元の実下側と正規化下側は同じ固定ホーン空間内で可逆比較される。
方針：同じ実入力点と実 encoder 像を可縮 Kan fiber 内で結ぶ。
規約：元の族の厳密対角回収や厳密切断は主張しない。
使われ方：正規化側で貼った比較を元の下側へ戻す。 -/
def verdierLowerCanonicalFamily_iso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h (verdierLowerCanonicalFamily d ℓ) := by
  let nt := (verdierLowerCanonicalEncode d).app (Opposite.op ⦋0⦌) ℓ
  let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace_isContractibleKan Δ[1]
      (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)).vertexIso
        (verdierLowerReconstructionPoint d) nt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)
  have hN : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierLowerCanonicalFamily d ℓ) = nt.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  exact hi ≪≫ eqToIso (congrArg HomotopyCategory.mk hN.symm)

end SerrePositivity.KST.Fibration
