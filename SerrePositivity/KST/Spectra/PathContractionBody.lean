module

public import SerrePositivity.KST.Spectra.PathSpace
public import SerrePositivity.KST.Spectra.PathReparametrization

/-!
概要：path space の収縮を評価前の写像族として構成する。
方針：区間変数の再パラメータ付けの後で path を評価する。
規約：始点と定数 path の両方の固定条件を検査する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：path を区間の点で評価する基礎単体集合の射。
方針：点つき内部 Hom の包含を通常の指数の随伴で uncurry する。
規約：基点の始点の条件は別の補題で保持する。
使われ方：Goerss–Jardine I §7。path space の収縮。 -/
def pathEvaluation (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ (basedPathSpace Y).right ⟶ Y.right :=
  MonoidalClosed.uncurry (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)

/-- 概要：path の評価は区間の始点で標的の基点となる。
方針：点つき Hom の等化子条件を使う。
規約：path のパラメータは任意。
使われ方：Goerss–Jardine I §7。収縮を点つき Hom へ戻す条件。 -/
theorem pathEvaluation_basepoint (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom ▷ (basedPathSpace Y).right ≫ pathEvaluation Y =
      toUnit (𝟙_ SSet.{u} ⊗ (basedPathSpace Y).right) ≫ Y.hom := by
  simpa only [Category.id_comp, pathEvaluation] using
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y (𝟙 (basedPathSpace Y).right)

/-- 概要：再パラメータ付けした path を評価する。
方針：区間と時刻に収縮を施した後で元の path を評価する。
規約：パラメータは path と時刻の直積。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。収縮の curry 前の写像族。 -/
def pathContractionBody (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u})) ⟶ Y.right :=
  pathReparametrization (basedPathSpace Y).right ≫ pathEvaluation Y

/-- 概要：再パラメータ付けした path は全時刻で始点を基点へ送る。
方針：区間の基点の固定と点つき path の始点条件を合成する。
規約：終点の条件は要求しない。
使われ方：Goerss–Jardine I §7。収縮を path space へ curry する条件。 -/
theorem pathContractionBody_basepoint (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom ▷ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u})) ≫
      pathContractionBody Y =
        toUnit (𝟙_ SSet.{u} ⊗ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u}))) ≫ Y.hom := by
  rw [pathContractionBody, ← Category.assoc, pathReparametrization_basepoint,
    Category.assoc, pathEvaluation_basepoint]
  simp only [comp_toUnit_assoc]

/-- 概要：収縮の時刻零の評価は標的の基点で定数。
方針：再パラメータ付けの時刻零の式と path の始点条件を使う。
規約：path に依存しない。
使われ方：Goerss–Jardine I §7。収縮の初端。 -/
theorem pathContractionBody_zero (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ (SSet.ι₀ : (basedPathSpace Y).right ⟶ _) ≫
      pathContractionBody Y = toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ (basedPathSpace Y).right) ≫
        Y.hom := by
  rw [pathContractionBody, ← Category.assoc, pathReparametrization_zero,
    Category.assoc, pathEvaluation_basepoint]
  simp only [comp_toUnit_assoc]

/-- 概要：収縮の時刻一の評価は元の path の評価。
方針：再パラメータ付けの時刻一の式を使う。
規約：path の全単体次数の等式。
使われ方：Goerss–Jardine I §7。収縮の終端。 -/
theorem pathContractionBody_one (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ (SSet.ι₁ : (basedPathSpace Y).right ⟶ _) ≫
      pathContractionBody Y = pathEvaluation Y := by
  rw [pathContractionBody, ← Category.assoc, pathReparametrization_one, Category.id_comp]

/-- 概要：収縮の評価は定数 path の上では全時刻で標的の基点。
方針：再パラメータ付けの自然性と内部 Hom の基点での評価を使う。
規約：時刻は自由に動かす。
使われ方：Goerss–Jardine I §7。基点固定ホモトピーの条件。 -/
theorem pathContractionBody_constant (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ ((basedPathSpace Y).hom ▷ (Δ[1] : SSet.{u})) ≫
      pathContractionBody Y =
        toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u}))) ≫ Y.hom := by
  rw [pathContractionBody, ← Category.assoc, pathReparametrization_natural, Category.assoc]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ (basedPathSpace Y).hom ≫
    MonoidalClosed.uncurry (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)) = _
  rw [PointedMapping.uncurry_parameter_basepoint]
  simp only [comp_toUnit_assoc]

end

end SerrePositivity.KST.Spectra
