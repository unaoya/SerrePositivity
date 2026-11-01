module
public import SerrePositivity.InfinityCategories.Simplicial.SimplexSubsetMap
public import SerrePositivity.KST.SConstruction.NecklaceSimplexIntervalTerminal

/-! # 元の有限部分集合から作る標準単体内の bead
概要：元の有限部分集合を、同じ最小・最大頂点の間の元の一 bead にする。
方針：元の一 bead と標準単体の同型に、元の昇順部分集合包含を合成する。
規約：元の濃度・全頂点像を保持。使われ方：HA 成分の元の cubical 生成射。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の有限部分集合の最小頂点から最大頂点への、同じ頂点像を持つ一 bead。 -/
def necklaceInSimplexSubset {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    NecklaceIn (Δ[n] : SSet.{u})
      (standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))))
      (standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega)))) where
  necklace := necklaceBead.{u} (I.card - 1)
  map := (NecklaceShape.singleSimplexIso _).hom ≫ simplexSubsetMap I hI
  map_first := (congrArg ((simplexSubsetMap.{u} I hI).app _)
    (simplexBeadFirstVertex_eq_standard _)).trans (simplexSubsetMap_first I hI)
  map_last := (congrArg ((simplexSubsetMap.{u} I hI).app _)
    (simplexBeadLastVertex_eq_standard _)).trans (simplexSubsetMap_last I hI)

/-- 元の部分集合 bead の augmentation は全高次単体で単射。 -/
instance necklaceInSimplexSubset_map_mono {n : ℕ}
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) : Mono (necklaceInSimplexSubset.{u} I hI).map :=
  inferInstanceAs (Mono ((NecklaceShape.singleSimplexIso _).hom ≫ simplexSubsetMap I hI))

/-- 元の部分集合 bead の次元は、同じ濃度から両端を除いた値。 -/
lemma necklaceInSimplexSubset_dimension {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (necklaceInSimplexSubset.{u} I hI).necklace.down.dimension = I.card - 2 :=
  (necklaceBead_dimension.{u} (I.card - 1)).trans (Nat.sub_sub I.card 1 1)

/-- 元の部分集合 bead の全頂点作用は、同じ元の昇順列挙。 -/
lemma necklaceInSimplexSubset_vertex {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (v : (NecklaceShape.single (I.card - 1)).Vertex) :
    necklaceSimplexVertexMap (necklaceInSimplexSubset.{u} I hI).necklace.down
      (necklaceInSimplexSubset I hI).map v = simplexSubsetOrder I hI v := rfl

end SerrePositivity.KST.SConstruction
