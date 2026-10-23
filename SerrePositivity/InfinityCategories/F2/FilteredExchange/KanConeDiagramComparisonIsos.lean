module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanConeDiagramLowerTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceTriangleIsoFacesEquality

/-!
概要：図式側の指定上下三角形の比較同型。
方針：同じ指定円柱の面と六辺の回収を使う。
規約：元の単体と指定同型を選び直さない。
使われ方：中央と最後の比較三単体の合成関係。
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
  (T : SSet.Homotopy c.val d.val) (K : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K)
/-- 概要：上側の指定三角形は対角射と図式成分・比較先の射の合成の同型。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
def kanConeDiagramUpperIso
    {i j : I} (f : i ⟶ j) :
    FunctorIso (kanConeDiagramDiagonal T f)
      (kanConeDiagramComponent T i ≫ G.map f) :=
  spaceInfinityTriangleIso_of_faces _ _ _ (kanConeDiagramUpperTriangle T f)
    (kanConeDiagramUpperTriangle_two T f) (kanConeDiagramUpperTriangle_zero T f)
    (kanConeDiagramUpperTriangle_one T f)
/-- 概要：下側の指定三角形は対角射と元の射・図式成分の合成の同型。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
def kanConeDiagramLowerIso
    {i j : I} (f : i ⟶ j) :
    FunctorIso (kanConeDiagramDiagonal T f)
      (F.map f ≫ kanConeDiagramComponent T j) :=
  spaceInfinityTriangleIso_of_faces _ _ _ (kanConeDiagramLowerTriangle T f)
    (kanConeDiagramLowerTriangle_two T f) (kanConeDiagramLowerTriangle_zero T f)
    (kanConeDiagramLowerTriangle_one T f)
/-- 概要：上側の指定同型は元の二単体の同型と型を含めて等しい。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
lemma kanConeDiagramUpperIso_heq
    {i j : I} (f : i ⟶ j) :
    HEq (kanConeDiagramUpperIso T f)
      (spaceInfinityTriangleIso (kanConeDiagramUpperTriangle T f)) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _
/-- 概要：下側の指定同型は元の二単体の同型と型を含めて等しい。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
lemma kanConeDiagramLowerIso_heq
    {i j : I} (f : i ⟶ j) :
    HEq (kanConeDiagramLowerIso T f)
      (spaceInfinityTriangleIso (kanConeDiagramLowerTriangle T f)) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _
/-- 概要：図式の比較正方形の指定同型。
方針：同じ対角関手を通る元の三角形の同型を使う。
規約：指定辺の類を保持する。
使われ方：三つの比較三単体の合成関係を合わせる。 -/
def kanConeDiagramComparisonIso
    {i j : I} (f : i ⟶ j) :
    FunctorIso (F.map f ≫ kanConeDiagramComponent T j)
      (kanConeDiagramComponent T i ≫ G.map f) :=
  (kanConeDiagramLowerIso T f).symm ≪≫ kanConeDiagramUpperIso T f

end SerrePositivity.InfinityCategories.F2
