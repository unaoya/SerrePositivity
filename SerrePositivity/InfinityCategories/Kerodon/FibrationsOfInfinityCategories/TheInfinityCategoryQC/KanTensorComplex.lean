module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.ProductTestFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：Kan 複体の直積の Kan 性。
方針：一方の射影の全ホーンの持ち上げ性から fibrant 性を回収する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：二つの Kan 複体の直積は Kan 複体。
方針：第二射影を fibration として表し標的の Kan 性を使う。
規約：選択済みの単体集合の直積を使う。
使われ方：原典の四角形の写像空間を Kan 対象に束縛する。 -/
lemma kanComplex_tensor (SX SY : SSet.{u}) [KanComplex SX] [KanComplex SY] :
    KanComplex (SX ⊗ SY) := by
  have : Fibration (snd SX SY) := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    intro A B i hi
    simp only [J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalProductProjection_hasLiftingProperty_horn SX SY n j
  exact isFibrant_of_fibration (snd SX SY)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
