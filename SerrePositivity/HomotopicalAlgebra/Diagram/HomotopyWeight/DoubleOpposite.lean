module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Reindex
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointReplacement

/-!
概要：右 frame に入力する重みの二重反対化を共有する。
方針：BarrattEccles と ComplexLimits の一致する宣言を、そのまま一箇所へ移す。
規約：小さい添字圏だけに依存し、値圏やモデル構造を引数に加えない。
使われ方：E 代数および複体の重み付き右 frame の end。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
variable (K : Type u) [SmallCategory K]

/-- 概要：重みを添字圏の二重反対圏へ移す（Hovey §5.4）。
方針：標準的な二重反対圏同値に沿う前合成を使う。
規約：各単体集合とその作用を変更しない。
使われ方：反対圏の実現と元の重みの添字を合わせる。 -/
abbrev doubleOpWeights : (K ⥤ SSet.{u}) ⥤ (Kᵒᵖᵒᵖ ⥤ SSet.{u}) :=
  (Functor.whiskeringLeft Kᵒᵖᵒᵖ K SSet.{u}).obj (opOpEquivalence K).functor

/-- 概要：選んだ一点重みを右 frame の反対添字へ移す（Hovey §5.4）。
方針：二重反対圏の同値に沿う前合成を使う。
規約：実際の射影 cofibrant な一点重みそのものを使う。
使われ方：重み付き end を図式全体の関手として評価する。 -/
abbrev framedLimitWeight := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)

/-- 概要：計算対象の二重反対化した一点重みは射影 cofibrant（Hovey §5.4）。
方針：添字の同値による保存と初期図式の同型を使う。
規約：元の自由境界の左類を保持する。
使われ方：一般 homotopy 極限の実現と写像空間の不変性。 -/
lemma framedLimitWeight_cofibrant :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖᵒᵖ).rlp.llp (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) := by
  have h := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.reindex_cofibration (opOpEquivalence K)
    (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K)
  let hi := initialIsInitial.isInitialObj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K) (⊥_ K ⥤ SSet.{u})
  let e : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj (⊥_ K ⥤ SSet.{u}) ≅ (⊥_ Kᵒᵖᵒᵖ ⥤ SSet.{u}) :=
    hi.uniqueUpToIso initialIsInitial
  let a : Arrow.mk ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).map (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K))) ≅
      Arrow.mk (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) :=
    Arrow.isoMk e (Iso.refl _) (hi.hom_ext _ _)
  exact ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖᵒᵖ).rlp.llp.arrow_mk_iso_iff a).mp h

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
