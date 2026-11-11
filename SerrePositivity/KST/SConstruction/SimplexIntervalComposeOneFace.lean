module
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeRefinement
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitFaceSign
public import SerrePositivity.KST.SConstruction.ConcreteCubeFaceConjugation

/-! # 元の厳密二区間の実合成 cube と共有頂点の一面
概要：元の二区間合成を同じ余次元一の cube として読み、元の共有頂点座標の一面と同定。
方針：全頂点を保つ refinement との一致と、元の右 bead 長による面座標を使う。
規約：元の全端点保存射・右端座標を保持。使われ方：厳密三頂点の実合成の Serre 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の厳密二区間の実合成は、元の全区間 cube の余次元一である。 -/
lemma simplexIntervalCompose_codimension {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    (necklaceBead.{u} (c.val - a.val)).down.dimension =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
        (necklaceBead (c.val - b.val))).down.dimension + 1 := by
  have hW := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedge_dimension
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val))
  have hp := necklaceBead_dimension.{u} (b.val - a.val)
  have hq := necklaceBead_dimension.{u} (c.val - b.val)
  have hr := necklaceBead_dimension.{u} (c.val - a.val)
  have ha : a.val < b.val := hab
  have hb : b.val < c.val := hbc
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - a.val)).dimension =
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedge
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val))).dimension + 1
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).dimension = b.val - a.val - 1 at hp
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)).dimension = c.val - b.val - 1 at hq
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - a.val)).dimension = c.val - a.val - 1 at hr
  omega

/-- 元の厳密二区間の共有頂点は、元の右区間の内部頂点数に等しい右端座標を持つ。 -/
def simplexIntervalComposeCoordinate {N : ℕ} (a b c : Fin (N + 1))
    (_hab : a < b) (_hbc : b < c) :
    Fin ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
      (necklaceBead (c.val - b.val))).down.dimension + 1) :=
  ⟨c.val - b.val - 1, by
    have hW := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedge_dimension
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val))
    have hp := necklaceBead_dimension.{u} (b.val - a.val)
    have hq := necklaceBead_dimension.{u} (c.val - b.val)
    change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).dimension = b.val - a.val - 1 at hp
    change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val)).dimension = c.val - b.val - 1 at hq
    change c.val - b.val - 1 < ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedge
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val))).dimension + 1
    omega⟩

/-- 元の厳密二区間の実合成 cube は、元の共有頂点の同じ標準一面。 -/
lemma simplexIntervalCompose_cube_one_face {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le) ≫
      (concreteCubeDimensionIso
        (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (c.val - a.val)).down.dimension)
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
          (necklaceBead (c.val - b.val))).down.dimension + 1))
        (simplexIntervalCompose_codimension a b c hab hbc)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
          (necklaceBead (c.val - b.val))).down.dimension
        (simplexIntervalComposeCoordinate.{u} a b c hab hbc) := by
  let p := b.val - a.val
  let q := c.val - b.val
  let d := c.val - a.val
  let T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q)
  have hp : 0 < p := by have ha : a.val < b.val := hab; omega
  have hq : 0 < q := by have hb : b.val < c.val := hbc; omega
  have he : p + q = d := by
    have ha : a.val < b.val := hab
    have hb : b.val < c.val := hbc
    omega
  have hc := simplexIntervalCompose_codimension.{u} a b c hab hbc
  have h₀ := congrArg (fun f => necklaceConcreteCubeMap f)
    (simplexIntervalComposeBeadHom_eq_refinement.{u} a b c hab.le hbc.le)
  have h₁ := necklaceConcreteCube.map_comp (necklaceWedgeBeadRefinement.{u} p q)
    (eqToHom (congrArg (necklaceBead.{u}) he))
  have h₂ := congrArg (fun f => necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u} p q) ≫ f)
    (necklaceBead_dimension_cube.{u} he)
  have h₃ := congrArg (fun f => f ≫ (concreteCubeDimensionIso
    (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} d).down.dimension)
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1)) hc).hom) (h₀.trans (h₁.trans h₂))
  have h₄ := congrArg (fun f => necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u} p q) ≫ f)
    (concreteCubeDimensionIso_hom_trans
      (congrArg (fun n => (necklaceBead.{u} n).down.dimension) he) hc)
  have hface := necklaceWedgeBeadRefinement_one_face.{u} p q hp hq
  have hi : Fin.cast (necklaceWedgeBead_codimension p q hp hq)
      (necklaceRefinementMissingCoordinate T (necklaceWedgeBeadSeam p q hp hq)) =
        simplexIntervalComposeCoordinate.{u} a b c hab hbc := by
    apply Fin.ext
    have h := necklaceWedgeBeadMissingCoordinate_val.{u} p q hp hq
    change (necklaceRefinementMissingCoordinate T
      (necklaceWedgeBeadSeam p q hp hq)).val + 1 = q at h
    change (necklaceRefinementMissingCoordinate T (necklaceWedgeBeadSeam p q hp hq)).val = q - 1
    omega
  exact h₃.trans ((Category.assoc _ _ _).trans
    (h₄.trans (hface.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension) hi))))

end SerrePositivity.KST.SConstruction
