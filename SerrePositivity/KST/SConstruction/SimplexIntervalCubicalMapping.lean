module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexIntervalTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # 元の標準単体の任意区間の cubical Hom
概要：元の a≤b の間の全 necklace の余極限を、元の (b−a−1) 立方体で回収する。
方針：元の区間 bead の終対象性と、非 joint 頂点数の元の次元移送を使う。
規約：一点区間と全生成射を保持。使われ方：native dg nerve の標準 dg 単体との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Simplicial SSet

/-- 元の区間 bead の生成射は、元の全 necklace の余極限との同型を与える。 -/
instance necklaceInSimplexInterval_cell_isIso {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    IsIso (necklaceCubicalCell (necklaceInSimplexInterval.{u} a b hab)) :=
  isIso_ι_of_isTerminal (necklaceInSimplexInterval_isTerminal a b hab)
    (necklaceCubicalDiagram (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))

/-- 元の区間 bead の表現可能立方体から、同じ両端間の実 cubical Hom への同型。 -/
def simplexIntervalCubicalCoreIso {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    necklaceCubicalSet.obj (necklaceBead.{u} (b.val - a.val)) ≅
      necklaceCubicalMapping (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  @asIso CubicalSet.{u} _ _ _ (necklaceCubicalCell (necklaceInSimplexInterval a b hab))
    (necklaceInSimplexInterval_cell_isIso a b hab)

/-- 元の全区間の実 cubical Hom を、元の (b−a−1) 次元の表現可能立方体で回収する。 -/
def simplexIntervalCubicalMappingIso {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) ≅
      necklaceCubicalMapping (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  cubicalYoneda.mapIso
      (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (b.val - a.val)).down.dimension)
        (necklaceBead_dimension.{u} (b.val - a.val)).symm) ≪≫
    simplexIntervalCubicalCoreIso a b hab

/-- 元の比較の順射は、元の次元移送と元の区間 bead の生成射の合成そのもの。 -/
lemma simplexIntervalCubicalMappingIso_hom {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (simplexIntervalCubicalMappingIso.{u} a b hab).hom =
      cubicalYoneda.map
          (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))
            (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (b.val - a.val)).down.dimension)
            (necklaceBead_dimension.{u} (b.val - a.val)).symm).hom ≫
        necklaceCubicalCell (necklaceInSimplexInterval a b hab) := rfl

/-- 元の全生成射を、元の区間 bead への可換三角形から厳密に回収する。 -/
lemma simplexIntervalCubicalCoreIso_cell {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) :
    necklaceCubicalSet.map (necklaceInToSimplexInterval a b hab T).necklaceHom ≫
        (simplexIntervalCubicalCoreIso a b hab).hom = necklaceCubicalCell T :=
  necklaceCubicalCell_relation (necklaceInToSimplexInterval a b hab T)

/-- 元の比較の逆方向は、全生成射で元の区間への具体的 cube 射を回収する。 -/
lemma simplexIntervalCubicalCoreIso_cell_inv {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) :
    necklaceCubicalCell T ≫ (simplexIntervalCubicalCoreIso a b hab).inv =
      necklaceCubicalSet.map (necklaceInToSimplexInterval a b hab T).necklaceHom := by
  have h := simplexIntervalCubicalCoreIso_cell a b hab T
  exact (congrArg (fun f => f ≫ (simplexIntervalCubicalCoreIso a b hab).inv) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => necklaceCubicalSet.map
        (necklaceInToSimplexInterval a b hab T).necklaceHom ≫ f)
        (simplexIntervalCubicalCoreIso a b hab).hom_inv_id).trans (Category.comp_id _)))

/-- 元の次元移送も含めた逆比較は、全生成射で元の具体的 cube 射を回収する。 -/
lemma simplexIntervalCubicalMappingIso_cell_inv {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) :
    necklaceCubicalCell T ≫ (simplexIntervalCubicalMappingIso a b hab).inv =
      necklaceCubicalSet.map (necklaceInToSimplexInterval a b hab T).necklaceHom ≫
        cubicalYoneda.map
          (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))
            (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (b.val - a.val)).down.dimension)
            (necklaceBead_dimension.{u} (b.val - a.val)).symm).inv :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ cubicalYoneda.map
      (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (b.val - a.val)).down.dimension)
        (necklaceBead_dimension.{u} (b.val - a.val)).symm).inv)
      (simplexIntervalCubicalCoreIso_cell_inv a b hab T))

end SerrePositivity.KST.SConstruction
