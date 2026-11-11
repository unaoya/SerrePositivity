module
public import SerrePositivity.KST.SConstruction.SimplexIntervalOperatorLaws
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaHom

/-! # 全単体作用素に関する元の Λ Hom 比較の自然性
概要：元の全ての面・退化の実 dg Hom 作用を、同じ具体的 cube の Serre 鎖で回収する。
方針：元の cubical 比較の可換性に Serre 関手を適用し、元の Yoneda 比較の自然性を使う。
規約：元の実 dg 関手と同じ余モノイド射。使われ方：native HA 単体への比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全区間の Serre Hom 比較は、元の全単体作用素の実 dg Hom 作用と可換。 -/
lemma simplexIntervalLambdaHomIso_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    (simplexIntervalLambdaHomIso A a b hab).hom ≫
        (cubicalLambdaMap A (stdSimplex.map θ)).map
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      (serreConcreteCubeComplexFunctor A).map (simplexIntervalCubeMap.{u} θ a b hab) ≫
        (simplexIntervalLambdaHomIso A (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab)).hom := by
  have h := congrArg ((cubicalSerreChains A).map)
    (simplexIntervalCubicalMappingIso_map.{u} θ a b hab)
  have ht := (cubicalSerreChainsCubeIso A).hom.naturality
    (simplexIntervalCubeMap.{u} θ a b hab)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f)
      ((cubicalSerreChains A).map_comp _ _).symm).trans
        ((congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f) h).trans
          ((congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f)
            ((cubicalSerreChains A).map_comp _ _)).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun f => f ≫ (cubicalSerreChains A).map
                  (simplexIntervalCubicalMappingIso (θ.toOrderHom a) (θ.toOrderHom b)
                    (θ.toOrderHom.monotone hab)).hom) ht.symm).trans
                      (Category.assoc _ _ _))))))

/-- 元の同じ全単体作用素の Hom 比較は、余モノイド値でも同じ可換四角形を持つ。 -/
lemma simplexIntervalLambdaHomComonoidIso_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    (simplexIntervalLambdaHomComonoidIso A a b hab).hom ≫
        cubicalLambdaMapComonoid A (stdSimplex.map θ)
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      (serreConcreteCubeFunctor A).map (simplexIntervalCubeMap.{u} θ a b hab) ≫
        (simplexIntervalLambdaHomComonoidIso A (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab)).hom := by
  have h := congrArg ((cubicalSerreComonoidFunctor A).map)
    (simplexIntervalCubicalMappingIso_map.{u} θ a b hab)
  have ht := (cubicalSerreComonoidCubeIso A).hom.naturality
    (simplexIntervalCubeMap.{u} θ a b hab)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (cubicalSerreComonoidCubeIso A).hom.app _ ≫ f)
      ((cubicalSerreComonoidFunctor A).map_comp _ _).symm).trans
        ((congrArg (fun f => (cubicalSerreComonoidCubeIso A).hom.app _ ≫ f) h).trans
          ((congrArg (fun f => (cubicalSerreComonoidCubeIso A).hom.app _ ≫ f)
            ((cubicalSerreComonoidFunctor A).map_comp _ _)).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun f => f ≫ (cubicalSerreComonoidFunctor A).map
                  (simplexIntervalCubicalMappingIso (θ.toOrderHom a) (θ.toOrderHom b)
                    (θ.toOrderHom.monotone hab)).hom) ht.symm).trans
                      (Category.assoc _ _ _))))))

end SerrePositivity.KST.SConstruction
