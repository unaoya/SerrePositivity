module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperShortFamilies
public import SerrePositivity.KST.Fibration.VerdierNativeDiagonalCoordinates
public import SerrePositivity.KST.Fibration.CoherentTriangleIntervalEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleCoherentEncoderNative

/-!
概要：動く実第二短辺と指定長 Hom 入力から、同じ全 S• 上側族を再構成する。
方針：元の core 包含・全 S• 比較合成端・coherent ホーンを実 canonical encoder へ渡す。
規約：入力は同じ実長 Hom fiber のデータであり、新しい存在仮定を主経路へ追加しない。
使われ方：K-6 c4 の全共有対角と指定有限端点を同時に回収する利用側。
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

/-- 概要：元の動く二短辺の実合成端を全入力で固定する長 Hom 空間。
方針：同じ F1 正本の合成端 fiber を元の実データで特殊化する。
規約：fiber の点を新たな存在仮定として要求しない。
使われ方：同じ相対合成から構成する長 Hom 入力の型。 -/
abbrev verdierMovingUpperLongSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) Δ[1]
    (verdierMovingUpperCompositeFamily d)

/-- 概要：同じ実ホーンを全パラメータで固定する上側二胞体族の空間。
方針：同じ元の動く二短辺への制限 fiber を取る。
規約：全短辺と非退化一単体を保持する。
使われ方：実 canonical encoder の行先。 -/
abbrev verdierMovingUpperTriangleSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace Δ[1] (verdierMovingUpperHorn d)

/-- 概要：同じ動く二短辺と長 Hom を持つ実 canonical 再構成写像。
方針：元の二短辺と厳密なホーン回収を F1 の公開実写像へ代入する。
規約：厳密切断は使わず、同じ encoder を保持する。
使われ方：元の長 Hom 全族から上側全二胞体族への実作用。 -/
def verdierMovingUpperEncode :
    verdierMovingUpperLongSpace d ⟶ verdierMovingUpperTriangleSpace d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (fullSRealizationKanObject d.left)
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) Δ[1]
    (verdierMovingUpperFirstFamily d) (verdierMovingUpperLastFamily d)
    (verdierMovingUpperHorn d) (verdierMovingUpperHorn_first d) (verdierMovingUpperHorn_last d)

variable (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌)

/-- 概要：同じ実入力と動く第二短辺を持つ実上側二胞体族。
方針：元の実 encoder の像の関手頂点を全族へ戻す。
規約：各時刻で二胞体を選び直さない。
使われ方：共有対角と有限端点の照合。 -/
def verdierMovingUpperFamily : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue ((verdierMovingUpperEncode d).app (Opposite.op ⦋0⦌) ℓ)

/-- 概要：同じ上側族の全ホーンは元の二つの実短辺そのもの。
方針：元の固定ホーン fiber の像を全族へ戻す。
規約：全次数の実写像の等式。
使われ方：動く第二短辺と固定包含の同時回収。 -/
theorem verdierMovingUpperFamily_horn :
    ((horn 2 (1 : Fin 3)).ι ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierMovingUpperFamily d ℓ = verdierMovingUpperHorn d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue_horn _

/-- 概要：同じ上側族の共有対角は元の指定長 Hom の直接 path 全族。
方針：実 encoder の全対角回収と所有する native path の座標等号を使う。
規約：元の全入力を保持し、encode/read の厳密切断は使わない。
使われ方：同じ実下側読出しの正規化対角との全時刻の貼り合わせ。 -/
theorem verdierMovingUpperFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierMovingUpperFamily d ℓ =
      verdierNativeDiagonalFamily d Δ[1]
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue ℓ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_diagonal
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (fullSRealizationKanObject d.left)
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) Δ[1]
    (verdierMovingUpperFirstFamily d) (verdierMovingUpperLastFamily d)
    (verdierMovingUpperHorn d) (verdierMovingUpperHorn_first d) (verdierMovingUpperHorn_last d) ℓ
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso_inv_first.{u, u + 1}).symm.trans
    (coherentTriangleInterval_up_first.{u})
  rw [hp] at h
  exact h

/-- 概要：同じ上側族の各時刻の全 native Hom は元の実入力そのもの。
方針：元の実 encoder の native 回収を同じ時刻へ代入する。
規約：直接端の値や Hom の類だけの一致には弱めない。
使われ方：指定有限端点の二胞体との照合。 -/
theorem verdierMovingUpperFamily_native (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue ℓ).app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_native
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (fullSRealizationKanObject d.left)
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) Δ[1]
    (verdierMovingUpperFirstFamily d) (verdierMovingUpperLastFamily d)
    (verdierMovingUpperHorn d) (verdierMovingUpperHorn_first d) (verdierMovingUpperHorn_last d) ℓ k

end SerrePositivity.KST.Fibration
