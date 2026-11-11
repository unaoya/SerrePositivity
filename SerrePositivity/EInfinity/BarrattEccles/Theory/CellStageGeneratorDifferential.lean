module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGeneratorCompatibility
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageDifferentialWeights
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageInclusionWeights

/-!
# 実際の付加の境界とセル段の K 平坦性

## 概要
Berger–Moerdijk 命題 4.1 のセル段で、付加生成元の微分は実際の境界の像である。

## 方針
生成元の照合・複体射の微分との可換性・境界の重みと段の包含の保存を使う。

## 規約
微分の式も重みの評価も、元のセル段の複体で述べる。

## 使われ方
cofibrant Barratt–Eccles 代数の台の K 平坦性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
open SerrePositivity.InfinityCategories
attribute [local implicit_reducible] operad Operad.cellStageGeneratorSpheres
variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- Each actual attaching boundary has the assigned bound of its new cell. -/
lemma cellBoundary_mem_weightSpan (hX : IsInitial X) (x : CellIndex c) :
    (Operad.attachedBoundary (c.attachCells x.1 x.2.1.down) x.2.2).val ∈
      basisWeightSpan (cellStageWordBasis c hX x.1 (Operad.cellDegree c x.1 x.2 + 1))
        (cellStageBasisWeight c hX x.1 (Operad.cellDegree c x.1 x.2 + 1))
        (cellStageWeight c hX x) := by
  have h : cellStageBasisLowerSpan c hX x.1 (Operad.cellDegree c x.1 x.2 + 1)
        (cellStageWeight c hX x) ≤
      basisWeightSpan (cellStageWordBasis c hX x.1 (Operad.cellDegree c x.1 x.2 + 1))
        (cellStageBasisWeight c hX x.1 (Operad.cellDegree c x.1 x.2 + 1))
        (cellStageWeight c hX x) :=
    Submodule.span_mono (Set.image_mono (fun _ h => Nat.le_of_lt h))
  exact h (cellBoundary_mem_lowerSpan c hX x)

/-- The differential of a presentation generator is the image of its actual attaching boundary. -/
lemma cellStageGeneratorValue_d (hX : IsInitial X) (j : J)
    (x : CellsBefore (Operad.CellsAt c) j)
    (z : sphereDegreeIndex.{u} (Operad.cellDegree c x.1 x.2) (Operad.cellDegree c x.1 x.2)) :
    (c.F.obj j).carrier.d (Operad.cellDegree c x.1 x.2) (Operad.cellDegree c x.1 x.2 + 1)
      (cellStageGeneratorValue c hX j (Operad.cellDegree c x.1 x.2) ⟨x, z⟩) =
      (c.F.map (homOfLE x.1.property.le)).hom.f (Operad.cellDegree c x.1 x.2 + 1)
        (Operad.attachedBoundary (c.attachCells x.1 x.2.1.down) x.2.2).val := by
  rw [cellStageGeneratorValue_eq_attached]
  let d := Operad.cellDegree c x.1 x.2
  let a := c.attachCells x.1 x.2.1.down
  let m := (c.F.map (homOfLE (Order.succ_le_of_lt x.1.property))).hom
  have hc := congrArg (fun g => g (Operad.attachedGenerator a x.2.2)) (m.comm d (d + 1))
  change (c.F.obj j).carrier.d d (d + 1) (m.f d (Operad.attachedGenerator a x.2.2)) =
    m.f (d + 1) ((c.F.obj (Order.succ x.1.val)).carrier.d d (d + 1)
      (Operad.attachedGenerator a x.2.2)) at hc
  erw [Operad.attachedGenerator_d a x.2.2] at hc
  have hm : (c.F.map (homOfLE (Order.le_succ x.1.val))).hom ≫ m =
      (c.F.map (homOfLE x.1.property.le)).hom := by
    change (c.F.map (homOfLE (Order.le_succ x.1.val)) ≫
      c.F.map (homOfLE (Order.succ_le_of_lt x.1.property))).hom = _
    rw [← c.F.map_comp]
    rfl
  change _ = (((c.F.map (homOfLE (Order.le_succ x.1.val))).hom ≫ m).f (d + 1))
    (Operad.attachedBoundary a x.2.2).val at hc
  rw [hm] at hc
  exact hc

/-- Every actual presentation generator differential has its assigned global weight bound. -/
lemma cellStageGeneratorValue_d_mem (hX : IsInitial X) (j : J) (i : ℤ)
    (z : (cellStageGeneratorWeightBasis c hX j).index i) :
    (c.F.obj j).carrier.d i (i + 1) (cellStageGeneratorValue c hX j i z) ∈
      basisWeightSpan (cellStageWordBasis c hX j (i + 1))
        (cellStageBasisWeight c hX j (i + 1))
        ((cellStageGeneratorWeightBasis c hX j).weight ⟨i, z⟩) := by
  obtain ⟨x, z⟩ := z
  have hi := sphereCoproductIndex_degree
    (fun x : CellsBefore (Operad.CellsAt c) j => Operad.cellDegree c x.1 x.2) i ⟨x, z⟩
  change i = Operad.cellDegree c x.1 x.2 at hi
  subst i
  rw [cellStageGeneratorValue_d]
  exact cellStageMap_preserves c hX x.1.property.le _ _
    (cellBoundary_mem_weightSpan c hX ⟨x.1.val, x.2⟩)

/-- Every actual cell stage starting from the initial algebra has a K-flat carrier. -/
lemma cellStageCarrierKFlat (hX : IsInitial X) (j : J) :
    complexKFlat A (c.F.obj j).carrier :=
  cellStageKFlat_of_generator_d c hX j (cellStageGeneratorValue_d_mem c hX j)

end SerrePositivity.EInfinity.BarrattEccles
