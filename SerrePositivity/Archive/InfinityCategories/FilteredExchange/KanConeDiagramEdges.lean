module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeTetrahedra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeDiagramDiagonalEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：Kan 錐の全円柱の図式成分と対角を元の Kan 射へ戻す。
方針：指定両端を揃え、coherent 辺の逆対応を使う。
規約：全一単体を保持。使われ方：中央・最後の比較三単体。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val)

/-- 概要：図式成分の両端を元の Kan 対象で指定する。
方針：頂点の式。規約：全一単体。使われ方：成分の読み戻し。 -/
def kanConeDiagramComponentEdge (i : I) : SpaceInfinity.{u}.Edge
    (coherentNerveVertex (F.obj i)) (coherentNerveVertex (G.obj i)) where
  edge := (coneHomotopyDiagramEdge T (ULift.up (ComposableArrows.mk₀ i))).edge
  src_eq := (coneHomotopyDiagramEdge T _).src_eq.trans
    ((kanDiagramCoherentNerve_vertex F i).trans (spaceInfinityVertex_eq_coherent _))
  tgt_eq := (coneHomotopyDiagramEdge T _).tgt_eq.trans
    ((kanDiagramCoherentNerve_vertex G i).trans (spaceInfinityVertex_eq_coherent _))

/-- 概要：図式成分の実際の Kan 射。
方針：辺の逆対応。規約：元の両端。使われ方：六つの境界射の同定。 -/
def kanConeDiagramComponent (i : I) : F.obj i ⟶ G.obj i :=
  coherentNerveEdgeToHom (kanConeDiagramComponentEdge T i)

/-- 概要：成分の読み戻しは元の全一単体を保持。
方針：辺と射の往復。規約：厳密な式。使われ方：三角形の面の同定。 -/
lemma kanConeDiagramComponent_edge (i : I) :
    (coherentNerveEdge (kanConeDiagramComponent T i)).edge =
      (coneHomotopyDiagramEdge T (ULift.up (ComposableArrows.mk₀ i))).edge :=
  congrArg SSet.Edge.edge (coherentNerveEdge_hom (kanConeDiagramComponentEdge T i))

/-- 概要：図式側の対角辺の両端を元の Kan 対象で指定する。
方針：頂点の式。規約：全一単体。使われ方：対角の読み戻し。 -/
def kanConeDiagramDiagonalEdge {i j : I} (f : i ⟶ j) : SpaceInfinity.{u}.Edge
    (coherentNerveVertex (F.obj i)) (coherentNerveVertex (G.obj j)) where
  edge := (coneDiagramDiagonalEdge T (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)).edge
  src_eq := (coneDiagramDiagonalEdge T _).src_eq.trans
    ((kanDiagramCoherentNerve_vertex F i).trans (spaceInfinityVertex_eq_coherent _))
  tgt_eq := (coneDiagramDiagonalEdge T _).tgt_eq.trans
    ((kanDiagramCoherentNerve_vertex G j).trans (spaceInfinityVertex_eq_coherent _))

/-- 概要：図式側の対角の実際の Kan 射。
方針：辺の逆対応。規約：元の両端。使われ方：共有面の同定。 -/
def kanConeDiagramDiagonal {i j : I} (f : i ⟶ j) : F.obj i ⟶ G.obj j :=
  coherentNerveEdgeToHom (kanConeDiagramDiagonalEdge T f)

/-- 概要：対角の読み戻しは元の全一単体を保持。
方針：辺と射の往復。規約：厳密な式。使われ方：三角形の長辺の同定。 -/
lemma kanConeDiagramDiagonal_edge {i j : I} (f : i ⟶ j) :
    (coherentNerveEdge (kanConeDiagramDiagonal T f)).edge =
      (coneDiagramDiagonalEdge T (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)).edge :=
  congrArg SSet.Edge.edge (coherentNerveEdge_hom (kanConeDiagramDiagonalEdge T f))

end SerrePositivity.InfinityCategories.F2
