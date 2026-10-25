module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.CountableStageComma
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.OppositeSimplexRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.F2.Compact.FiniteUniverse

/-!
概要：可算段階関手の局所左 Kan 図式を有限段階の図式へ比較する。
方針：コンマ圏の同値、nerve の左 Kan 比較、宇宙比較を順に合成する。
規約：元の射影と元の有限段階の包含に厳密に可換とする。
使われ方：全有限図式の保存余極限から可算形状の局所左 Kan 余極限を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：有限段階の反対単体圏から元の局所左 Kan 形状への比較。
方針：段階のコンマ圏への逆比較と二つの形状同型を合成する。
規約：指定された自然数の頂点を保持する。使われ方：局所図式の余極限の縮約。 -/
def countableStageKanComparison (B : SSet.{u}) [Countable B.S] (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (TransportSimplexCategory (countableFiniteStage B n).toSSet)ᵒᵖ) ⟶
        leftKanShape ((SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (countableSimplexStageFunctor B)))
            (ULift.up (nerveVertex (ULift.up n))) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (countableStageSimplexToComma B n) ≫
      (F1B.nerveLeftKanShapeIso (countableSimplexStageFunctor B) (ULift.up n)).hom) ≫
    (Idempotent.leftKanShapeUniverseIso (nerveMap (countableSimplexStageFunctor B))
      (nerveVertex (ULift.up n))).hom

/-- 概要：有限段階から局所左 Kan 形状への比較は right cofinal。
方針：コンマ圏の同値の随伴から native な cofinal 性を得て形状同型と合成する。
規約：通常の final 性だけで止めない。使われ方：元の局所余錐の比較。 -/
lemma countableStageKanComparison_isRightCofinal (B : SSet.{u}) [Countable B.S] (n : ℕ) :
    IsRightCofinal (countableStageKanComparison B n) := by
  have h : IsRightCofinal (nerveMap (countableStageSimplexToComma B n)) := by
    apply nerveMap_isRightCofinal_of_initial_comma
    intro a
    let adj := (countableStageCommaEquivalence B n).toAdjunction
    exact ⟨StructuredArrow.mk (adj.unit.app a),
      ⟨mkInitialOfLeftAdjoint (countableStageSimplexToComma B n) adj a⟩⟩
  exact (Ind.isRightCofinal_ulift _ (h.comp (isRightCofinal_of_isIso
    (F1B.nerveLeftKanShapeIso (countableSimplexStageFunctor B) (ULift.up n)).hom))).comp
      (isRightCofinal_of_isIso
        (Idempotent.leftKanShapeUniverseIso (nerveMap (countableSimplexStageFunctor B))
          (nerveVertex (ULift.up n))).hom)

/-- 概要：局所左 Kan 比較は元の有限段階の包含への射影を保つ。
方針：二つの形状同型の射影則とコンマ圏の厳密な射影則を合成する。
規約：同型を介さない実際の射の等式。使われ方：制限図式の同定。 -/
lemma countableStageKanComparison_projection (B : SSet.{u}) [Countable B.S] (n : ℕ) :
    countableStageKanComparison B n ≫
      leftKanProjection ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (countableSimplexStageFunctor B)))
          (ULift.up (nerveVertex (ULift.up n))) =
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (transportSimplexFunctor (countableFiniteStage B n).ι).op) := by
  rw [countableStageKanComparison, Category.assoc,
    Idempotent.leftKanShapeUniverseIso_projection, ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [Category.assoc, F1B.nerveLeftKanShapeIso_hom_projection]
  change nerveMap (countableStageSimplexToComma B n ⋙
    CostructuredArrow.proj (countableSimplexStageFunctor B) (ULift.up n)) = _
  rw [countableStageSimplexToComma_proj]

/-- 概要：全有限図式に保存余極限があれば段階関手の全局所図式も保存余極限を持つ。
方針：cofinal 比較で有限段階の反対単体圏へ制限し、その局所化を使う。
規約：有限段階の nerve 自体に有限性を仮定しない。
使われ方：有限余極限から可算形状の保存余極限を構成する局所段階。 -/
lemma hasPreservedColimit_countableStage_leftKan
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), Ind.HasPreservedColimit U D)
    (B : SSet.{u}) [Countable B.S]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ X) (n : ℕ) :
    Ind.HasPreservedColimit U (leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (countableSimplexStageFunctor B)))
      ((SSet.uliftFunctor.{u + 1, u}).map (oppositeSimplexRestriction B) ≫ F)
      (ULift.up (nerveVertex (ULift.up n)))) := by
  apply (hasPreservedColimit_iff_rightCofinalRestriction U _
    (countableStageKanComparison_isRightCofinal B n) _).mpr
  have he : countableStageKanComparison B n ≫ leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (countableSimplexStageFunctor B)))
      ((SSet.uliftFunctor.{u + 1, u}).map (oppositeSimplexRestriction B) ≫ F)
      (ULift.up (nerveVertex (ULift.up n))) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (oppositeSimplexRestriction (countableFiniteStage B n).toSSet) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (countableFiniteStage B n).ι) ≫ F) := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, countableStageKanComparison_projection,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      oppositeSimplexRestriction_naturality, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [he]
  apply (hasPreservedColimit_iff_oppositeSimplexRestriction U _ _).mp
  have : (countableFiniteStage B n).toSSet.op.Finite :=
    ⟨Finite.of_equiv (countableFiniteStage B n).toSSet.N SSet.N.opEquiv.symm.toEquiv⟩
  have : ((SSet.uliftFunctor.{u + 1, u}).obj
      (countableFiniteStage B n).toSSet.op).Finite :=
    (Compact.finite_ulift_iff _).mpr inferInstance
  exact hfin _ _

end SerrePositivity.InfinityCategories.F2.Presentable
