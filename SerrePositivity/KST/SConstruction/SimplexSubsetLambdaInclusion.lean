module
public import SerrePositivity.KST.SConstruction.SimplexSubsetCubicalInclusion
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCell

/-! # 元の部分集合包含と同端点の Serre 生成射
概要：元の濃度−2 次元の包含射は、元の同じ Hom への Serre・余モノイド生成射と可換。
方針：元の cubical 生成射の可換性と、元の Serre 比較の自然性を合成する。
規約：元の鎖射と余モノイド射を一致させる。使われ方：HA の削除項の実回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の指定端点の Hom に入る、元の部分集合の同じ Serre 生成射。 -/
def simplexSubsetLambdaCellAt {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    serreCubeComplex A (I.card - 2) ⟶
      homObject A (CubicalLambda A (Δ[n] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  (cubicalSerreChainsCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ≫
    (cubicalSerreChains A).map (simplexSubsetCubicalCellAt I a b hI ha hb)

/-- 元の最小・最大端点では、元の同じ Serre 生成射を厳密に回収する。 -/
lemma simplexSubsetLambdaCellAt_canonical {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) :
    simplexSubsetLambdaCellAt A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl = simplexSubsetLambdaCell A I hI := rfl

/-- 元の指定端点の同じ Serre 生成射を、元の Hom 余モノイドへの射に束ねる。 -/
def simplexSubsetLambdaCellComonoidAt {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    serreCubeComonoid A (I.card - 2) ⟶
      cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  (cubicalSerreComonoidCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ≫
    (cubicalSerreComonoidFunctor A).map (simplexSubsetCubicalCellAt I a b hI ha hb)

/-- 元の余モノイド値の生成射は、元の同じ鎖射を基礎の射に持つ。 -/
lemma simplexSubsetLambdaCellComonoidAt_hom {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (simplexSubsetLambdaCellComonoidAt A I a b hI ha hb).hom =
      simplexSubsetLambdaCellAt A I a b hI ha hb := rfl

variable {n : ℕ} (I J : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
  (haI : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
  (hbI : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
  (haJ : a = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
  (hbJ : b = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))

/-- 元の部分集合包含の Serre 鎖は、元の同端点の同じ生成射と厳密に可換。 -/
lemma simplexSubsetLambdaCellAt_inclusion :
    (serreConcreteCubeComplexFunctor A).map
        (simplexSubsetCubeInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ) ≫
      simplexSubsetLambdaCellAt A J a b hJ haJ hbJ =
        simplexSubsetLambdaCellAt A I a b hI haI hbI := by
  have h := congrArg ((cubicalSerreChains A).map)
    (simplexSubsetCubeInclusion_cell.{u} I J a b hI hJ hIJ haI hbI haJ hbJ)
  have ht := (cubicalSerreChainsCubeIso A).hom.naturality
    (simplexSubsetCubeInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cubicalSerreChains A).map
      (simplexSubsetCubicalCellAt J a b hJ haJ hbJ)) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f)
          ((cubicalSerreChains A).map_comp _ _).symm).trans
            (congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f) h))))

/-- 元の同じ部分集合包含は、元の同端点の余モノイド値の生成射とも厳密に可換。 -/
lemma simplexSubsetLambdaCellComonoidAt_inclusion :
    (serreConcreteCubeFunctor A).map
        (simplexSubsetCubeInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ) ≫
      simplexSubsetLambdaCellComonoidAt A J a b hJ haJ hbJ =
        simplexSubsetLambdaCellComonoidAt A I a b hI haI hbI := by
  have h := congrArg ((cubicalSerreComonoidFunctor A).map)
    (simplexSubsetCubeInclusion_cell.{u} I J a b hI hJ hIJ haI hbI haJ hbJ)
  have ht := (cubicalSerreComonoidCubeIso A).hom.naturality
    (simplexSubsetCubeInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cubicalSerreComonoidFunctor A).map
      (simplexSubsetCubicalCellAt J a b hJ haJ hbJ)) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (cubicalSerreComonoidCubeIso A).hom.app _ ≫ f)
          ((cubicalSerreComonoidFunctor A).map_comp _ _).symm).trans
            (congrArg (fun f => (cubicalSerreComonoidCubeIso A).hom.app _ ≫ f) h))))

end SerrePositivity.KST.SConstruction
