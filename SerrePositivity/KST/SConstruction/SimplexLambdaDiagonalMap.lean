module
public import SerrePositivity.KST.SConstruction.SimplexDiagonalLambdaHom

/-! # 元の対角 Λ Hom から任意 dg 対象の自己 Hom への実鎖射
概要：元の対角 Hom の増大と指定対象の単位を合成し、元の単位と dg 後合成を保つ。
方針：元の増大 dg 関手の単位保存と、対角の単位射の実同型性を使う。
規約：元の全対角 Hom を保持。使われ方：native HA 逆 dg 関手の対角分岐。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の対角 Λ Hom の増大と指定対象の元の単位からなる実鎖射。 -/
def simplexLambdaDiagonalMap {N : ℕ} (a : Fin (N + 1)) (X : D) :
    homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) ⟶ homObject A D X X :=
  (cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) ≫
    eId (Complex A) X

/-- 元の対角 Λ Hom の単位は、指定対象の元の単位へ写る。 -/
lemma simplexLambdaDiagonalMap_id {N : ℕ} (a : Fin (N + 1)) (X : D) :
    eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) ≫
      simplexLambdaDiagonalMap A a X = eId (Complex A) X := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ eId (Complex A) X)
      ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map_id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a))).trans
        (Category.id_comp _))

/-- 元の対角 Λ Hom の実鎖射は、厳密 dg 関手による後合成と可換。 -/
lemma simplexLambdaDiagonalMap_post {N : ℕ} (a : Fin (N + 1)) (X : D)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E) :
    simplexLambdaDiagonalMap A a (F.obj X) =
      simplexLambdaDiagonalMap A a X ≫ F.map X X := by
  have h := congrArg (fun f => (cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) ≫ f) (F.map_id X)
  exact ((Category.assoc _ _ _).trans h).symm

/-- 元の実 dg 関手の対角 Hom 作用は、同じ対象の元の増大・単位による鎖射。 -/
lemma simplexLambdaDiagonalMap_recovery {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) (a : Fin (N + 1)) :
    simplexLambdaDiagonalMap A a (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) =
      F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) := by
  apply (cancel_epi
    (eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a))).1
  exact (simplexLambdaDiagonalMap_id A a (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a))).trans
    (F.map_id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)).symm

end SerrePositivity.KST.SConstruction
