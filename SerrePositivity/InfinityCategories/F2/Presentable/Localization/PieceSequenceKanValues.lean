module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PieceSequenceFiberKan
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SmallShapeLeftKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPartialColimitFamily

/-!
概要：部分 poset 列の全空間に沿う Kan 拡張の値を、元の指定段の実余極限として回収する。
方針：共終な fiber 比較を宇宙持ち上げし、局所普遍余錐を制限する。
規約：Kan 延長の値そのものを厳密な余錐頂点とする。使われ方：交互細分列の余極限族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 元の fiber 比較を、同じ大きい局所 Kan 添字へ持ち上げる。 -/
def pieceSequenceFiberKanComparisonUniverse
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (A n).val) ⟶ leftKanShape
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalIndex A)))
      (ULift.up (nerveVertex (ULift.up n))) :=
  (SSet.uliftFunctor.{u + 1, u}).map (pieceSequenceFiberKanComparison A n) ≫
    (Idempotent.leftKanShapeUniverseIso _ (nerveVertex (ULift.up n))).hom

/-- 同じ大きい局所比較は right cofinal。 -/
lemma pieceSequenceFiberKanComparisonUniverse_isRightCofinal
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) (n : ℕ) :
    IsRightCofinal (pieceSequenceFiberKanComparisonUniverse A n) :=
  (Ind.isRightCofinal_ulift _ (pieceSequenceFiberKanComparison_isRightCofinal A hA n)).comp
    (isRightCofinal_of_trivialKanFibration
      (Idempotent.leftKanShapeUniverseIso _ (nerveVertex (ULift.up n))).hom)

/-- 元の大きい局所比較も、全空間の指定 fiber 包含を厳密に回収する。 -/
lemma pieceSequenceFiberKanComparisonUniverse_projection
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    pieceSequenceFiberKanComparisonUniverse A n ≫ leftKanProjection
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalIndex A)))
      (ULift.up (nerveVertex (ULift.up n))) =
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalFiber A n)) := by
  dsimp only [pieceSequenceFiberKanComparisonUniverse]
  rw [Category.assoc, Idempotent.leftKanShapeUniverseIso_projection,
    ← Functor.map_comp, pieceSequenceFiberKanComparison_projection]

/-- 指定された全 Kan 延長の値を、同じ段の実余極限頂点として回収する。 -/
lemma pieceSequence_leftKan_value_isPartialColimit
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A)
    {C : SSet.{u + 1}} [Quasicategory C]
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (PieceSequenceTotal A)) ⟶ C}
    {G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C}
    {β : SSet.Homotopy F
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalIndex A)) ≫ G)}
    (hβ : IsLeftKanExtension
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalIndex A))) F G β)
    (n : ℕ) :
    ∃ a : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (pieceSequenceTotalFiber A n)) ≫ F),
      IsColimitCone a ∧ a.vertex = G.app _ (ULift.up (nerveVertex (ULift.up n))) := by
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (ULift.up (nerveVertex (ULift.up n)))
  let q := pieceSequenceFiberKanComparisonUniverse A n
  have hq := pieceSequenceFiberKanComparisonUniverse_isRightCofinal A hA n
  have hd := (Ind.isColimitCone_iff_restrict_rightCofinal q hq c).mp hc
  have he : q ≫ leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalIndex A))) F
      (ULift.up (nerveVertex (ULift.up n))) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalFiber A n)) ≫ F := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, pieceSequenceFiberKanComparisonUniverse_projection]
  refine ⟨coherentCoconeOfDiagramEq he (c.restrict q),
    (coherentCoconeOfDiagramEq_isColimit_iff he _).mp hd, ?_⟩
  rw [coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict]
  exact hv

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
