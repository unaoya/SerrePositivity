module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPieceLeftKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPieceFiberCofinal
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：元の部分余極限を、一つの全単位変換を持つ coherent な関手として組み立てる。
方針：同じ fiber の cofinal 比較を宇宙持ち上げし、左 Kan の局所普遍余錐を制限する。
規約：元の部分図式を全単体で回収し、延長の指定した値を厳密な頂点とする。
使われ方：濃度変更の μ-filtered な部分余極限表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]
  {C : SSet.{u + 1}} [Quasicategory C]

/-- 同じ fiber の局所比較を、元の大きい左 Kan 添字へ持ち上げる。 -/
def smallPieceFiberKanComparisonUniverse (A : SmallFilteredPieces κ μ I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve A.val) ⟶ leftKanShape
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece))
      (ULift.up (nerveVertex A)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallPieceFiberKanComparison A) ≫
    (Idempotent.leftKanShapeUniverseIso _ (nerveVertex A)).hom

lemma smallPieceFiberKanComparisonUniverse_isRightCofinal (A : SmallFilteredPieces κ μ I) :
    IsRightCofinal (smallPieceFiberKanComparisonUniverse A) :=
  (Ind.isRightCofinal_ulift _ (smallPieceFiberKanComparison_isRightCofinal A)).comp
    (isRightCofinal_of_trivialKanFibration
      (Idempotent.leftKanShapeUniverseIso _ (nerveVertex A)).hom)

/-- 元の大きい局所比較も、同じ全空間の fiber 包含を厳密に保つ。 -/
lemma smallPieceFiberKanComparisonUniverse_projection (A : SmallFilteredPieces κ μ I) :
    smallPieceFiberKanComparisonUniverse A ≫ leftKanProjection
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece))
      (ULift.up (nerveVertex A)) =
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (smallFilteredTotalFiber A)) := by
  dsimp only [smallPieceFiberKanComparisonUniverse]
  rw [Category.assoc, Idempotent.leftKanShapeUniverseIso_projection,
    ← Functor.map_comp, smallPieceFiberKanComparison_projection]

/-- 一つの左 Kan 拡張の指定した値は、元の fiber 制限の余極限の厳密な頂点となる。 -/
lemma smallPiece_leftKan_value_isPartialColimit
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredTotal κ μ I)) ⟶ C}
    {G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredPieces κ μ I)) ⟶ C}
    {β : SSet.Homotopy F
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece) ≫ G)}
    (hβ : IsLeftKanExtension
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece)) F G β)
    (A : SmallFilteredPieces κ μ I) :
    ∃ c : JoinCocone
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (smallFilteredTotalFiber A)) ≫ F),
      IsColimitCone c ∧ c.vertex = G.app _ (ULift.up (nerveVertex A)) := by
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (ULift.up (nerveVertex A))
  let q := smallPieceFiberKanComparisonUniverse A
  have hq := smallPieceFiberKanComparisonUniverse_isRightCofinal A
  have hd := (Ind.isColimitCone_iff_restrict_rightCofinal q hq c).mp hc
  have he : q ≫ leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece)) F
      (ULift.up (nerveVertex A)) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (smallFilteredTotalFiber A)) ≫ F := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, smallPieceFiberKanComparisonUniverse_projection]
  refine ⟨HomotopyLimits.coherentCoconeOfDiagramEq he (c.restrict q),
    (HomotopyLimits.coherentCoconeOfDiagramEq_isColimit_iff he _).mp hd, ?_⟩
  rw [HomotopyLimits.coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict]
  exact hv

/-- 元の図式の全ての部分余極限を、一つの coherent な関手と全単位変換で実現する。 -/
lemma exists_smallPartialColimitFamily (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredPieces κ μ I)) ⟶ C)
      (β : SSet.Homotopy
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalValue) ≫ D)
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece) ≫ G)),
      IsLeftKanExtension
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalValue) ≫ D) G β ∧
      ∀ A : SmallFilteredPieces κ μ I, ∃ c : JoinCocone (smallFilteredPartialDiagram D A),
        IsColimitCone c ∧ c.vertex = G.app _ (ULift.up (nerveVertex A)) := by
  obtain ⟨G, β, hβ⟩ := smallPiece_exists_leftKanExtension hC
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalValue) ≫ D)
  refine ⟨G, β, hβ, fun A ↦ ?_⟩
  obtain ⟨c, hc, hv⟩ := smallPiece_leftKan_value_isPartialColimit hβ A
  let he := smallFilteredTotalDiagram_restrict_fiber D A
  refine ⟨HomotopyLimits.coherentCoconeOfDiagramEq he c,
    (HomotopyLimits.coherentCoconeOfDiagramEq_isColimit_iff he c).mp hc, ?_⟩
  rw [HomotopyLimits.coherentCoconeOfDiagramEq_vertex]
  exact hv

end SerrePositivity.InfinityCategories.F2.Presentable
