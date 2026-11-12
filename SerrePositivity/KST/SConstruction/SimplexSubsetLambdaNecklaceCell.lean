module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCellAtDimension
public import SerrePositivity.KST.SConstruction.NecklaceLambdaCell
public import SerrePositivity.KST.SConstruction.SerreCubeChainFace

/-! # 元の部分集合 Serre 生成射と同じ necklace cell
概要：指定端点・指定次元の部分集合生成射を、元の同じ necklace cell と比較する。
方針：元の Serre 比較の自然性と次元等号移送を照合し、表示だけの違いを除く。
規約：元の全生成射と両端を保持。使われ方：区間 Hom 比較と native HA 復元の逆律。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の同じ necklace augmentation は、元の全次数の実 Serre cell を異種等号で保つ。 -/
lemma necklaceLambdaCell_heq_of_eq {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (h : T = U) :
    HEq (necklaceLambdaCell A T) (necklaceLambdaCell A U) := by
  cases h
  rfl

/-- 元の指定端点の部分集合生成射は、同じ次元移送と元の necklace cell の合成。 -/
lemma simplexSubsetLambdaCellAt_necklace {N : ℕ} (I : Finset (Fin (N + 1)))
    (a b : Fin (N + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    simplexSubsetLambdaCellAt A I a b hI ha hb =
      eqToHom (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} I hI).symm) ≫
        necklaceLambdaCell A (necklaceInSimplexSubsetAt.{u} I a b hI ha hb) := by
  let f := (simplexSubsetCubeDimensionIso.{u} I hI).hom
  have h := (cubicalSerreChainsCubeIso A).hom.naturality f
  have hd : (serreConcreteCubeComplexFunctor A).map f = eqToHom
      (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} I hI).symm) :=
    serreCubeComplexMap_dimension_inv A (necklaceInSimplexSubset_dimension.{u} I hI)
  have h₁ : simplexSubsetLambdaCellAt A I a b hI ha hb =
      (cubicalSerreChainsCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ≫
        ((cubicalSerreChains A).map (cubicalYoneda.map f) ≫
          (cubicalSerreChains A).map
            (necklaceCubicalCell (necklaceInSimplexSubsetAt.{u} I a b hI ha hb))) :=
    congrArg (fun g => (cubicalSerreChainsCubeIso A).hom.app _ ≫ g)
      ((cubicalSerreChains A).map_comp _ _)
  exact h₁.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (cubicalSerreChains A).map
      (necklaceCubicalCell (necklaceInSimplexSubsetAt.{u} I a b hI ha hb))) h.symm).trans
        ((congrArg (fun g => (g ≫ (cubicalSerreChainsCubeIso A).hom.app _) ≫
          (cubicalSerreChains A).map
            (necklaceCubicalCell (necklaceInSimplexSubsetAt.{u} I a b hI ha hb))) hd).trans
              (Category.assoc _ _ _))))

/-- 元の指定次元の生成射は、元の同じ necklace cell を異種等号で保持する。 -/
lemma simplexSubsetLambdaCellAtDimension_necklace_heq {N : ℕ} (I : Finset (Fin (N + 1)))
    (a b : Fin (N + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (d : ℕ) (hd : d = I.card - 2) :
    HEq (simplexSubsetLambdaCellAtDimension A I a b hI ha hb d hd)
      (necklaceLambdaCell A (necklaceInSimplexSubsetAt.{u} I a b hI ha hb)) :=
  (eqToHom_comp_heq _ _).trans
    ((heq_of_eq (simplexSubsetLambdaCellAt_necklace A I a b hI ha hb)).trans
      (eqToHom_comp_heq _ _))

end SerrePositivity.KST.SConstruction
