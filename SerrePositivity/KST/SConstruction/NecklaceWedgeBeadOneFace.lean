module
public import SerrePositivity.KST.SConstruction.NecklaceRefinementOneFace
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeFunctor

/-! # 元の二 bead の連結から一 bead への標準一面
概要：元の共有頂点を持つ二つの bead の実 refinement は、同じ共有頂点座標の標準一面。
方針：元の連結の joints が両端と共有頂点の三つであることを証明して一般判定を使う。
規約：左右とも正長の元の bead、共有頂点は元の joint。使われ方：HA の分割合成項。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の二 bead の連結の joints は、元の両端と共有頂点そのもの。 -/
lemma necklaceWedgeBead_joints (p q : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single q)).joints = {0, p, p + q} := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.image_insert,
    Finset.image_singleton, add_zero]
  ext k
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- 元の二つの正長 bead の共有頂点は、全体の一 bead の同じ内部頂点。 -/
def necklaceWedgeBeadSeam (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).NonjointVertex :=
  ⟨⟨p, by change p < p + q + 1; omega⟩, by
    change p ∉ ({0, p + q} : Finset ℕ)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega⟩

/-- 元の連結した二 bead から同じ全頂点を持つ一 bead への実端点保存射。 -/
def necklaceWedgeBeadRefinement (p q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q) ⟶ necklaceBead (p + q) :=
  necklaceBeadRefinement _

/-- 元の二 bead の実 refinement の全頂点作用は、同じ元の頂点番号の恒等写像。 -/
lemma necklaceWedgeBeadRefinement_vertex (p q : ℕ)
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q)).down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (necklaceWedgeBeadRefinement.{u} p q) v = v := rfl

/-- 元の二つの正長 bead の連結の cube は、元の全体の一 bead の cube の余次元一。 -/
lemma necklaceWedgeBead_codimension (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).dimension =
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single q)).dimension + 1 :=
  necklaceRefinementMissingCoordinate_codimension
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{0} p) (necklaceBead q))
    (necklaceWedgeBeadSeam p q hp hq) (necklaceWedgeBead_joints p q)

/-- 元の二 bead の実 refinement cube 射は、元の同じ共有頂点座標の標準一面。 -/
lemma necklaceWedgeBeadRefinement_one_face (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    let T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q)
    necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u} p q) ≫
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).dimension)
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1))
          (necklaceWedgeBead_codimension p q hp hq)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension
        (Fin.cast (necklaceWedgeBead_codimension p q hp hq)
          (necklaceRefinementMissingCoordinate T (necklaceWedgeBeadSeam p q hp hq))) :=
  necklaceRefinement_cube_one_face (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q))
    (necklaceWedgeBeadSeam p q hp hq) (necklaceWedgeBead_joints p q)

/-- 元の二 bead の同じ Serre refinement 射は、元の共有頂点座標の標準鎖一面。 -/
lemma necklaceWedgeBeadRefinement_serre_one_face (A : Type u) [CommRing A]
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    let T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q)
    serreConcreteCubeMap A (necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u} p q)) ≫
        serreCubeDimensionMap A (necklaceWedgeBead_codimension p q hp hq) =
      serreCubeFace A true T.down.dimension
        (Fin.cast (necklaceWedgeBead_codimension p q hp hq)
          (necklaceRefinementMissingCoordinate T (necklaceWedgeBeadSeam p q hp hq))) :=
  necklaceRefinement_serre_one_face (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q))
    (necklaceWedgeBeadSeam p q hp hq) A (necklaceWedgeBead_joints p q)

end SerrePositivity.KST.SConstruction
