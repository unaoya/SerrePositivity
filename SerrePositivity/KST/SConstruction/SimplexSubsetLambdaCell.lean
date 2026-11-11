module
public import SerrePositivity.KST.SConstruction.SimplexSubsetCubicalCell
public import SerrePositivity.KST.SConstruction.CubicalLambdaComonoids
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImage

/-! # 元の有限部分集合の Serre 生成射と HA 向きの元
概要：元の部分集合の実生成射を元の Λ の Hom 複体へ送り、次数 2−濃度の元を作る。
方針：元の Serre 比較・余モノイド値関手・向き補正した最高生成元を使う。
規約：元の有限部分集合と実鎖射を保持。使われ方：実 dg 関手からの native HA 成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の部分集合の同じ cubical 生成射の Serre 鎖である、元の Λ Hom への実鎖射。 -/
def simplexSubsetLambdaCell {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    serreCubeComplex A (I.card - 2) ⟶
      homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega)))) :=
  (cubicalSerreChainsCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ≫
    (cubicalSerreChains A).map (simplexSubsetCubicalCell I hI)

/-- 元の部分集合の同じ Serre 生成射は、元の Hom 余モノイドへの射。 -/
def simplexSubsetLambdaCellComonoid {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    serreCubeComonoid A (I.card - 2) ⟶
      cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega)))) :=
  (cubicalSerreComonoidCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ≫
    (cubicalSerreComonoidFunctor A).map (simplexSubsetCubicalCell I hI)

/-- 元の余モノイド値の生成射の基礎の鎖射は、同じ元の部分集合の生成射。 -/
lemma simplexSubsetLambdaCellComonoid_hom {n : ℕ}
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (simplexSubsetLambdaCellComonoid A I hI).hom = simplexSubsetLambdaCell A I hI := rfl

/-- 元の部分集合の最高生成元の、元の Λ Hom 内の HA 向きと次数を持つ実像。 -/
def simplexSubsetLambdaGenerator {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega))))).X (2 - (I.card : ℤ)) :=
  eqToHom (congrArg (fun k =>
    (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega))))).X k)
    (show -((I.card - 2 : ℕ) : ℤ) = 2 - (I.card : ℤ) by omega))
      (serreCubeTopCellImage A _ (I.card - 2) (simplexSubsetLambdaCell A I hI))

end SerrePositivity.KST.SConstruction
