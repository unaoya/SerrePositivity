module
public import SerrePositivity.KST.SConstruction.SimplexIntervalCompositionCoordinates
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceSimplexVertices
public import SerrePositivity.KST.SConstruction.NecklaceWedgeBeadOneFace

/-! # 元の厳密区間合成と全頂点を保つ refinement
概要：元の二区間の合成 necklace 射を、同じ二 bead の実 refinement と次元移送で回収。
方針：元の全頂点作用の恒等性と、necklace 射の全頂点判定を使う。
規約：元の全高次単体と端点保存射を保持。使われ方：厳密三頂点の合成と実一面の比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の bead 長の等号移送は、元の同じ頂点番号を保持する。 -/
lemma necklaceBead_dimension_vertex {p q : ℕ} (h : p = q)
    (v : (necklaceBead.{u} p).down.Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (eqToHom (congrArg (necklaceBead.{u}) h)) v).val = v.val := by
  cases h
  exact congrArg Fin.val (congrFun (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_id (necklaceBead.{u} p)) v)

/-- 元の二区間の実合成射は、元の全頂点を保つ refinement と同じ bead 長の移送。 -/
lemma simplexIntervalComposeBeadHom_eq_refinement {N : ℕ} (a b c : Fin (N + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    simplexIntervalComposeBeadHom.{u} a b c hab hbc =
      necklaceWedgeBeadRefinement.{u} (b.val - a.val) (c.val - b.val) ≫
        eqToHom (congrArg (necklaceBead.{u})
          (show b.val - a.val + (c.val - b.val) = c.val - a.val by
            have _ha : a.val ≤ b.val := hab
            have _hb : b.val ≤ c.val := hbc
            omega)) := by
  have he : b.val - a.val + (c.val - b.val) = c.val - a.val := by
    have _ha : a.val ≤ b.val := hab
    have _hb : b.val ≤ c.val := hbc
    omega
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_injective
  funext v
  apply Fin.ext
  have h := congrArg Fin.val (congrFun (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp
    (necklaceWedgeBeadRefinement.{u} (b.val - a.val) (c.val - b.val))
    (eqToHom (congrArg (necklaceBead.{u})
      (show b.val - a.val + (c.val - b.val) = c.val - a.val by
        have _ha : a.val ≤ b.val := hab
        have _hb : b.val ≤ c.val := hbc
        omega)))) v)
  exact (simplexIntervalComposeBeadHom_vertex a b c hab hbc v).trans
    (h.trans ((necklaceBead_dimension_vertex he
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (necklaceWedgeBeadRefinement.{u} (b.val - a.val) (c.val - b.val)) v)).trans
      (congrArg Fin.val (necklaceWedgeBeadRefinement_vertex _ _ v)))).symm

/-- 元の bead 長の等号移送は、元の具体的 cube の同じ次元等号の移送。 -/
lemma necklaceBead_dimension_cube {p q : ℕ} (h : p = q) :
    necklaceConcreteCubeMap (eqToHom (congrArg (necklaceBead.{u}) h)) =
      (concreteCubeDimensionIso
        (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} p).down.dimension)
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} q).down.dimension)
        (congrArg (fun n => (necklaceBead.{u} n).down.dimension) h)).hom := by
  cases h
  exact necklaceConcreteCube.map_id (necklaceBead.{u} p)

end SerrePositivity.KST.SConstruction
