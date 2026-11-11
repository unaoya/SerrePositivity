module
public import SerrePositivity.KST.SConstruction.NecklaceIsoCubicalMapping
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceVertices
public import SerrePositivity.KST.SConstruction.ConcreteCubeDimensionIso
public import Mathlib.Order.Interval.Finset.Nat

/-! # 元の標準単体の両端間の cubical mapping object
概要：標準 n 単体の元の始端から終端への全 necklace 図式を、元の (n−1) 立方体へ戻す。
方針：元の単体全体の終対象性と元の非 joint 頂点の数を照合する。
規約：n=0 の点も含む。使われ方：Λ の標準単体と native dg nerve の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits _root_.Simplicial SSet

/-- 元の標準 n 単体全体を一つの bead として持つ necklace。 -/
abbrev necklaceBead (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} := ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n⟩

/-- 元の標準単体の始零単体を、元の一 bead 同型で指定する。 -/
def simplexBeadFirstVertex (n : ℕ) : (Δ[n] : SSet.{u}) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n).hom.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).firstVertex

/-- 元の標準単体の終零単体を、元の一 bead 同型で指定する。 -/
def simplexBeadLastVertex (n : ℕ) : (Δ[n] : SSet.{u}) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n).hom.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).lastVertex

/-- 元の始零単体の頂点番号は元の零番。 -/
lemma simplexBeadFirstVertex_val (n : ℕ) : simplexBeadFirstVertex.{u} n 0 = 0 := rfl

/-- 元の終零単体の頂点番号は元の n 番。 -/
lemma simplexBeadLastVertex_val (n : ℕ) : simplexBeadLastVertex.{u} n 0 = Fin.last n := rfl

/-- 元の標準 n 単体の非 joint 頂点数は n−1 であり、点でも成立する。 -/
lemma necklaceBead_dimension (n : ℕ) : (necklaceBead.{u} n).down.dimension = n - 1 := by
  have h : ((Finset.range (n + 1)).filter (fun j => j ∉ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).joints)) =
      Finset.Ioo 0 n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single,
      Finset.mem_insert, Finset.mem_singleton, not_or, Finset.mem_Ioo]
    omega
  change ((Finset.range (n + 1)).filter (fun j => j ∉ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).joints)).card = _
  rw [h, Nat.card_Ioo]
  omega

/-- 元の標準単体の両端間の全 necklace の余極限を、元の表現可能立方体へ戻す同型。 -/
def simplexBeadCubicalMappingIso (n : ℕ) :
    cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1)) ≅
      necklaceCubicalMapping (Δ[n] : SSet.{u})
        (simplexBeadFirstVertex n) (simplexBeadLastVertex n) :=
  cubicalYoneda.mapIso
      (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1))
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} n).down.dimension)
        (necklaceBead_dimension.{u} n).symm) ≪≫
    necklaceIsoCubicalMappingIso (necklaceBead.{u} n) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n)

/-- 元の標準単体の比較の正方向は、元の次元移送と全体の生成射を回収する。 -/
lemma simplexBeadCubicalMappingIso_hom (n : ℕ) :
    (simplexBeadCubicalMappingIso.{u} n).hom =
      cubicalYoneda.map
          (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1))
            (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} n).down.dimension)
            (necklaceBead_dimension.{u} n).symm).hom ≫
        necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInOfIso (necklaceBead.{u} n)
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n)) := rfl

/-- 元の比較の逆方向は、標準単体内の全生成射で元の具体的 cube 射を回収する。 -/
lemma simplexBeadCubicalMappingIso_cell_inv (n : ℕ)
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (simplexBeadFirstVertex n) (simplexBeadLastVertex n)) :
    necklaceCubicalCell T ≫ (simplexBeadCubicalMappingIso n).inv =
      necklaceCubicalSet.map
          ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInToOfIso (necklaceBead.{u} n)
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n) T).necklaceHom) ≫
        cubicalYoneda.map
          (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1))
            (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} n).down.dimension)
            (necklaceBead_dimension.{u} n).symm).inv := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ cubicalYoneda.map
      (@concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1))
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} n).down.dimension)
        (necklaceBead_dimension.{u} n).symm).inv)
      (necklaceIsoCubicalMappingIso_cell_inv (necklaceBead.{u} n)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n) T))

end SerrePositivity.KST.SConstruction
