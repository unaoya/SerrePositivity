module

public import SerrePositivity.EInfinity.Hammock.WordForwardTripleCollapse
public import SerrePositivity.EInfinity.Hammock.SegmentSubdivision
public import SerrePositivity.EInfinity.Hammock.SegmentAdjacent

/-!
# 元の三列の区間合成と同じ三つの射の合成

概要：元の三つの forward 列の区間合成が元の同じ三つの隣接射の合成であることを証明する。
方針：元の区間を二度分割し、各一列の回収を使う。
規約：端点の移送を含む元の Segment.map を使う。
使われ方：三列 collapse の元の列への回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardTriple
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y : C}
  (S : Zigzag W Word.ForwardTriple.word X Y)

lemma segment_composite :
    Segment.map .forward S (0 : Fin 4) (Fin.last 3) (by decide)
      (fun i _ _ => Word.ForwardTriple.direction i) =
    Direction.arrow .forward S (0 : Fin 3) (Word.ForwardTriple.direction 0) ≫
      Direction.arrow .forward S (1 : Fin 3) (Word.ForwardTriple.direction 1) ≫
        Direction.arrow .forward S (2 : Fin 3) (Word.ForwardTriple.direction 2) := by
  rw [Segment.map_comp .forward S (0 : Fin 4) (1 : Fin 4) (Fin.last 3) (by decide) (by decide)]
  rw [Segment.map_comp .forward S (1 : Fin 4) (2 : Fin 4) (Fin.last 3) (by decide) (by decide)]
  have h0 : Segment.map .forward S (0 : Fin 4) (1 : Fin 4) (by decide)
      (fun i _ _ => Word.ForwardTriple.direction i) =
      Direction.arrow .forward S (0 : Fin 3) (Word.ForwardTriple.direction 0) :=
    Segment.map_adjacent .forward S (0 : Fin 3) (Word.ForwardTriple.direction 0)
  have h1 : Segment.map .forward S (1 : Fin 4) (2 : Fin 4) (by decide)
      (fun i _ _ => Word.ForwardTriple.direction i) =
      Direction.arrow .forward S (1 : Fin 3) (Word.ForwardTriple.direction 1) :=
    Segment.map_adjacent .forward S (1 : Fin 3) (Word.ForwardTriple.direction 1)
  have h2 : Segment.map .forward S (2 : Fin 4) (Fin.last 3) (by decide)
      (fun i _ _ => Word.ForwardTriple.direction i) =
      Direction.arrow .forward S (2 : Fin 3) (Word.ForwardTriple.direction 2) :=
    Segment.map_adjacent .forward S (2 : Fin 3) (Word.ForwardTriple.direction 2)
  rw [h0, h1, h2]

end SerrePositivity.EInfinity.Hammock.ForwardTriple
