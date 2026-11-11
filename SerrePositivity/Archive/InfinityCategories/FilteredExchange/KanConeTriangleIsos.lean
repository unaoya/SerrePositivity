module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeFirstTetrahedronEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIsoFacesEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TetrahedronEdgeFaces

/-!
概要：Kan 錐の元の三角形、上側比較、第一共有面の指定ホモトピー類の同型。
方針：三辺を元の射に揃えて精密化の辺の類を読む。
規約：元の二単体の値と型付きの一致を保持。使われ方：四面の合成則への代入。
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

/-- 概要：元の錐の指定三角形のホモトピー類の同型。
方針：三辺を読み戻す。規約：元の値。使われ方：第一合成則の上面。 -/
def kanNativeConeTriangleIso (c : JoinCone (kanDiagramCoherentNerve F))
    (K : KanObject.{u}) (hc : c.vertex = coherentNerveVertex K) {i j : I} (f : i ⟶ j) :
    FunctorIso (kanNativeConeLeg c K hc j) (kanNativeConeLeg c K hc i ≫ F.map f) :=
  spaceInfinityTriangleIso_of_faces _ _ _ (kanNativeConeTriangle c f)
    (kanNativeConeTriangle_two c K hc f) (kanNativeConeTriangle_zero c f)
    (kanNativeConeTriangle_one c K hc f)

/-- 概要：錐の指定同型は元の二単体の値を保持。
方針：端点の輸送。規約：型付きの一致。使われ方：上面の同型の同定。 -/
lemma kanNativeConeTriangleIso_heq (c : JoinCone (kanDiagramCoherentNerve F))
    (K : KanObject.{u}) (hc : c.vertex = coherentNerveVertex K) {i j : I} (f : i ⟶ j) :
    HEq (kanNativeConeTriangleIso c K hc f)
      (spaceInfinityTriangleIso (kanNativeConeTriangle c f)) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

variable (T : SSet.Homotopy c.val d.val) (K L : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K) (hd : d.vertex = coherentNerveVertex L)
  (a : K ⟶ L) (ha : (coneHomotopyApexEdge T).edge = (coherentNerveEdge a).edge)

/-- 概要：上側の指定三角形のホモトピー類の同型。
方針：元の三辺の同定。規約：元の比較辺。使われ方：第一合成則の左右の面。 -/
def kanConeUpperIso (i : I) :
    FunctorIso (kanConeHomotopyDiagonal T K hc i) (a ≫ kanNativeConeLeg d L hd i) :=
  spaceInfinityTriangleIso_of_faces _ _ _ (coneHomotopyUpperTriangle T
    (ULift.up (ComposableArrows.mk₀ i)))
    ((coneHomotopyUpperTriangle_two T _).trans ha)
    ((coneHomotopyUpperTriangle_zero T _).trans (kanNativeConeLeg_edge d L hd i).symm)
    ((coneHomotopyUpperTriangle_one T _).trans (kanConeHomotopyDiagonal_edge T K hc i).symm)

/-- 概要：上側の指定同型は元の二単体の値を保持。
方針：端点の輸送。規約：型付きの一致。使われ方：側面の同型の同定。 -/
lemma kanConeUpperIso_heq (i : I) :
    HEq (kanConeUpperIso T K L hc hd a ha i) (spaceInfinityTriangleIso
      (coneHomotopyUpperTriangle T (ULift.up (ComposableArrows.mk₀ i)))) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

/-- 概要：最初と中央の共有面の指定同型。
方針：同じ対角射と図式射で三辺を表す。規約：元の共有面。使われ方：内部同型の消去。 -/
def kanConeFirstInteriorIso {i j : I} (f : i ⟶ j) :
    FunctorIso (kanConeHomotopyDiagonal T K hc j)
      (kanConeHomotopyDiagonal T K hc i ≫ G.map f) :=
  spaceInfinityTriangleIso_of_faces _ _ _ (SpaceInfinity.δ 1 (kanConeTetrahedron T f 0))
    ((tetrahedronEdge02_eq _).trans (kanConeFirst_edge02 T K hc f))
    ((tetrahedronEdge23_eq _).trans (kanConeFirst_edge23 T f))
    ((tetrahedronEdge03_eq _).trans (kanConeFirst_edge03 T K hc f))

/-- 概要：共有面の指定同型は元の二単体の値を保持。
方針：端点の輸送。規約：型付きの一致。使われ方：第一と中央の同型の接続。 -/
lemma kanConeFirstInteriorIso_heq {i j : I} (f : i ⟶ j) :
    HEq (kanConeFirstInteriorIso T K hc f)
      (spaceInfinityTriangleIso (SpaceInfinity.δ 1 (kanConeTetrahedron T f 0))) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
