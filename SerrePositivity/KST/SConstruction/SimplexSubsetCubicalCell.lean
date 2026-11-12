module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubset
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping

/-! # 元の有限部分集合 bead の cubical 生成射
概要：元の部分集合の濃度−2 次元の表現可能立方体から、同じ両端の実 Hom へ送る。
方針：元の次元移送と元の全 necklace の余極限の生成射を合成する。
規約：元の生成射を逆移送で回収。使われ方：HA 成分の元の Serre 生成射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の部分集合の数値次元を、同じ元の bead の次元へ移す同型。 -/
def simplexSubsetCubeDimensionIso {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2) ≅
      (necklaceConcreteCube.{u}).obj (necklaceInSimplexSubset.{u} I hI).necklace :=
  @concreteCubeDimensionIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceInSimplexSubset.{u} I hI).necklace.down.dimension)
    (necklaceInSimplexSubset_dimension.{u} I hI).symm

/-- 元の部分集合の表現可能立方体から、同じ元の necklace Hom への実生成射。 -/
def simplexSubsetCubicalCell {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ⟶
      necklaceCubicalMapping (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega)))) :=
  cubicalYoneda.map (simplexSubsetCubeDimensionIso.{u} I hI).hom ≫
    necklaceCubicalCell (necklaceInSimplexSubset I hI)

/-- 元の次元移送の逆は、元の同じ部分集合 bead の生成射そのものを回収する。 -/
lemma simplexSubsetCubicalCell_recovery {n : ℕ}
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    cubicalYoneda.map (simplexSubsetCubeDimensionIso.{u} I hI).inv ≫
        simplexSubsetCubicalCell I hI = necklaceCubicalCell (necklaceInSimplexSubset I hI) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ necklaceCubicalCell (necklaceInSimplexSubset I hI))
      (cubicalYoneda.mapIso (simplexSubsetCubeDimensionIso.{u} I hI)).inv_hom_id).trans
        (Category.id_comp _))

end SerrePositivity.KST.SConstruction
