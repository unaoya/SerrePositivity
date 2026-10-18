module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGCoherenceData
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDiagram

/-!
概要：KST §3.1 の全有限重なりに沿う O(m) の指定推移単元。
方針：行先の pivot 座標で始点の pivot を表す既存単元の整数冪を使う。
規約：共変な加群遷移では O(1) の frame_i を S_i^{(k)} frame_k に送る。
使われ方：構造図式加群の捻りを実際の dg 加群として構成する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：選択 pivot による有限重なりの係数環。
方針：既存の局所化環の表示を非空有限重なりへ適用する。
規約：KST §3.1。使われ方：捻りの推移単元の係数環。 -/
abbrev FiniteOverlapVertexRing (T : FiniteOverlapIndex I) :=
  FiniteOverlapRing R (finiteOverlapIndexPivot T) T.val

/-- 概要：全有限重なりの包含に沿う O(m) の指定推移単元。
方針：行先の座標で表す始点 pivot の単元を m 乗する。
規約：KST §3.1、m は全整数。使われ方：捻り dg 加群の遷移の scalar。 -/
def finiteOverlapTwistUnit {T U : FiniteOverlapIndex I} (h : T ≤ U) (m : ℤ) :
    (FiniteOverlapVertexRing R U)ˣ :=
  (finiteOverlapUnit R (finiteOverlapIndexPivot U) U.val (finiteOverlapIndexPivot T)
    (h (finiteOverlapIndexPivot_mem T))) ^ m

/-- 概要：O(1) の推移単元の値は行先の座標での始点 pivot 座標。
方針：整数冪 1 と既存の重なり単元の値の公式を使う。
規約：KST §3.1。使われ方：捻りの符号・向きの確認。 -/
theorem finiteOverlapTwistUnit_one_val {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    (finiteOverlapTwistUnit R h 1 : FiniteOverlapVertexRing R U) =
      finiteOverlapCoordinates R (finiteOverlapIndexPivot U) U.val (finiteOverlapIndexPivot T) := by
  simp only [finiteOverlapTwistUnit, zpow_one, finiteOverlapUnit_val]
  rfl

/-- 概要：恒等包含の捻り推移単元は全整数で 1。
方針：同じ pivot の座標が 1 であることを使う。
規約：KST §3.1。使われ方：捻りの恒等遷移。 -/
theorem finiteOverlapTwistUnit_id (T : FiniteOverlapIndex I) (m : ℤ) :
    finiteOverlapTwistUnit R (le_refl T) m = 1 := by
  simp only [finiteOverlapTwistUnit, finiteOverlapUnit_self, one_zpow]

/-- 概要：O(0) の推移単元は全包含で 1。
方針：単元の零乗を使う。
規約：KST §3.1。使われ方：構造図式加群への特殊化。 -/
theorem finiteOverlapTwistUnit_zero {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapTwistUnit R h 0 = 1 := by
  simp only [finiteOverlapTwistUnit, zpow_zero]

/-- 概要：捻りの和の推移単元は二つの推移単元の積。
方針：単元群の整数冪の加法則を使う。
規約：KST §3.1。使われ方：捻りの合成と逆捻り。 -/
theorem finiteOverlapTwistUnit_add {T U : FiniteOverlapIndex I} (h : T ≤ U) (m n : ℤ) :
    finiteOverlapTwistUnit R h (m + n) =
      finiteOverlapTwistUnit R h m * finiteOverlapTwistUnit R h n :=
  zpow_add _ m n

/-- 概要：逆捻りの推移単元は元の推移単元の逆。
方針：単元群の負の整数冪の公式を使う。
規約：KST §3.1。使われ方：捻り自己同値の逆。 -/
theorem finiteOverlapTwistUnit_neg {T U : FiniteOverlapIndex I} (h : T ≤ U) (m : ℤ) :
    finiteOverlapTwistUnit R h (-m) = (finiteOverlapTwistUnit R h m)⁻¹ :=
  zpow_neg _ m

/-- 概要：捻りの指定推移単元は全整数で三重重なりの cocycle を満たす。
方針：既存の基底変換単元の合成公式を整数冪で送り、可換性と冪の自然性を使う。
規約：KST §3.1、係数環の移送を Units.map で明示する。
使われ方：捻った図式加群の合成律。 -/
theorem finiteOverlapTwistUnit_comp {T U V : FiniteOverlapIndex I}
    (h : T ≤ U) (g : U ≤ V) (m : ℤ) :
    finiteOverlapTwistUnit R g m *
      Units.map (finiteOverlapChartMap R (finiteOverlapIndexPivot U) (finiteOverlapIndexPivot V)
        g (finiteOverlapIndexPivot_mem U)).toRingHom.toMonoidHom
        (finiteOverlapTwistUnit R h m) =
      finiteOverlapTwistUnit R (h.trans g) m := by
  have he := congrArg (fun s : (FiniteOverlapVertexRing R V)ˣ => s ^ m)
    (finiteOverlapDGTransition_unit_comp R (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
      (finiteOverlapIndexPivot V) h g
      (finiteOverlapIndexPivot_mem T) (finiteOverlapIndexPivot_mem U))
  simpa only [finiteOverlapTwistUnit, mul_zpow, map_zpow] using he

end SerrePositivity.KST.DerivedBlowup
