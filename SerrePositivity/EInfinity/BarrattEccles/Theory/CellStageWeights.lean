module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGradedBasis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellularGenerators
public import SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedBasisKFlat

/-!
# 実際のセルの境界から選ぶ重み

## 概要
Berger–Moerdijk 命題 4.1 のセル代数で、境界の実際の有限な基底展開から重みを選ぶ。

## 方針
各境界に現れる入力の語を取り出し、先行段への整礎再帰を適用する。

## 規約
各セルの識別子を保持し、単項式で入力が重複する回数を数える。

## 使われ方
セル代数の微分と、台の K 平坦性に使う基底の重みの照合。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra DifferentialGraded

variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The actual cell indices in the whole relative cell complex. -/
abbrev CellIndex := Σ j, Operad.CellsAt c j

/-- A cell is earlier if it was attached at an earlier stage. -/
def earlierCell (x y : CellIndex c) : Prop := x.1 < y.1

lemma earlierCell_wellFounded : WellFounded (earlierCell c) :=
  InvImage.wf (fun x : CellIndex c => x.1) wellFounded_lt

/-- The earlier cell labels in the input word of a basis vector at one stage. -/
def cellWordLabels (j : J) (i : ℤ)
    (x : SchurWordIndex
      (SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) j =>
        Operad.cellDegree c y.1 y.2)) i) :
    List {y : CellIndex c // y.1 < j} :=
  (schurWordInputs x).map (fun y =>
    ⟨⟨y.2.1.1.val, y.2.1.2⟩, y.2.1.1.property⟩)

/-- The actual boundary of the cell, expanded in the specified basis of its source stage. -/
def cellBoundaryNormalForm (hX : IsInitial X) (x : CellIndex c) :
    SchurWordIndex
      (SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) x.1 =>
        Operad.cellDegree c y.1 y.2)) (Operad.cellDegree c x.1 x.2 + 1) →₀ A :=
  (cellStageWordBasis c hX x.1 (Operad.cellDegree c x.1 x.2 + 1)).repr
    (Operad.attachedBoundary (c.attachCells x.1 x.2.1.down) x.2.2).val

/-- The finite set of earlier input words appearing in the actual cell boundary. -/
def cellBoundaryWords (hX : IsInitial X) (x : CellIndex c) :
    Finset (List {y : CellIndex c // earlierCell c y x}) := by
  classical
  exact (cellBoundaryNormalForm c hX x).support.image
    (cellWordLabels c x.1 (Operad.cellDegree c x.1 x.2 + 1))

/-- The prescribed degree bound in the weight recursion. -/
def cellDegreeLowerBound (x : CellIndex c) : ℕ :=
  Int.toNat (Operad.cellDegree c x.1 x.2)

/-- The weights are chosen from the actual boundary expansions, with the degree bound included. -/
def cellStageWeight (hX : IsInitial X) : CellIndex c → ℕ :=
  cellularWeightAbove (earlierCell_wellFounded c) (cellDegreeLowerBound c)
    (cellBoundaryWords c hX)

/-- Every cell weight dominates the cochain degree of that generator. -/
lemma cellDegree_le_cellStageWeight (hX : IsInitial X) (x : CellIndex c) :
    Operad.cellDegree c x.1 x.2 ≤ (cellStageWeight c hX x : ℤ) := by
  have h := le_cellularWeightAbove (earlierCell_wellFounded c) (cellDegreeLowerBound c)
    (cellBoundaryWords c hX) x
  change Int.toNat (Operad.cellDegree c x.1 x.2) ≤ cellStageWeight c hX x at h
  have h' : Operad.cellDegree c x.1 x.2 ≤
      (Int.toNat (Operad.cellDegree c x.1 x.2) : ℤ) := by omega
  omega

/-- Each input word in the actual boundary has weight strictly smaller than its cell. -/
lemma cellBoundaryWord_weight_lt (hX : IsInitial X) (x : CellIndex c)
    (m : SchurWordIndex
      (SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) x.1 =>
        Operad.cellDegree c y.1 y.2)) (Operad.cellDegree c x.1 x.2 + 1))
    (hm : m ∈ (cellBoundaryNormalForm c hX x).support) :
    ((cellWordLabels c x.1 (Operad.cellDegree c x.1 x.2 + 1) m).map
      (fun y => cellStageWeight c hX y.val)).sum < cellStageWeight c hX x := by
  classical
  apply boundaryWeight_lt_cellularWeightAbove
    (earlierCell_wellFounded c) (cellDegreeLowerBound c) (cellBoundaryWords c hX)
  exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

/-- The global cell weight on the homogeneous inputs of a fixed stage. -/
def cellStageInputWeight (hX : IsInitial X) (j : J)
    (x : Σ i, SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) j =>
      Operad.cellDegree c y.1 y.2) i) : ℕ :=
  cellStageWeight c hX ⟨x.2.1.1.val, x.2.1.2⟩

/-- The weight of a specified basis word in the actual cell stage. -/
def cellStageBasisWeight (hX : IsInitial X) (j : J) (i : ℤ)
    (x : SchurWordIndex
      (SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) j =>
        Operad.cellDegree c y.1 y.2)) i) : ℕ :=
  schurWordWeight (cellStageInputWeight c hX j) x

lemma cellStageBasisWeight_eq_labels (hX : IsInitial X) (j : J) (i : ℤ)
    (x : SchurWordIndex
      (SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) j =>
        Operad.cellDegree c y.1 y.2)) i) :
    cellStageBasisWeight c hX j i x =
      ((cellWordLabels c j i x).map (fun y => cellStageWeight c hX y.val)).sum := by
  simp only [cellStageBasisWeight, schurWordWeight, cellWordLabels, List.map_map]
  rfl

/-- The actual cell word weight dominates the cochain degree of its basis vector. -/
lemma cellStageBasisDegree_le_weight (hX : IsInitial X) (j : J) (i : ℤ)
    (x : SchurWordIndex
      (SphereCoproductIndex (fun y : CellsBefore (Operad.CellsAt c) j =>
        Operad.cellDegree c y.1 y.2)) i) :
    i ≤ (cellStageBasisWeight c hX j i x : ℤ) := by
  apply degree_le_schurWordWeight
  intro y
  have hd := sphereCoproductIndex_degree
    (fun z : CellsBefore (Operad.CellsAt c) j => Operad.cellDegree c z.1 z.2) y.1 y.2
  change y.1 = Operad.cellDegree c y.2.1.1 y.2.1.2 at hd
  rw [hd]
  exact cellDegree_le_cellStageWeight c hX ⟨y.2.1.1.val, y.2.1.2⟩

/-- The span of the specified basis words of weight strictly below the bound. -/
def cellStageBasisLowerSpan (hX : IsInitial X) (j : J) (i : ℤ) (n : ℕ) :
    Submodule A ((c.F.obj j).carrier.X i) :=
  Submodule.span A ((cellStageWordBasis c hX j i) ''
    {x | cellStageBasisWeight c hX j i x < n})

/-- The actual boundary is in the span of words of strictly smaller weight than its cell. -/
lemma cellBoundary_mem_lowerSpan (hX : IsInitial X) (x : CellIndex c) :
    (Operad.attachedBoundary (c.attachCells x.1 x.2.1.down) x.2.2).val ∈
      cellStageBasisLowerSpan c hX x.1 (Operad.cellDegree c x.1 x.2 + 1)
        (cellStageWeight c hX x) := by
  classical
  apply (Module.Basis.mem_span_image
    (cellStageWordBasis c hX x.1 (Operad.cellDegree c x.1 x.2 + 1))).mpr
  intro m hm
  change cellStageBasisWeight c hX x.1 (Operad.cellDegree c x.1 x.2 + 1) m < _
  rw [cellStageBasisWeight_eq_labels]
  exact cellBoundaryWord_weight_lt c hX x m hm

end SerrePositivity.EInfinity.BarrattEccles
