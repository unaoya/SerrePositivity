module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaGeneratorNecklace
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaInclusion

/-! # 元の濃度次元の Serre 射と native HA 成分
概要：指定端点と指定次数の native HA 成分を、元の濃度−2 次元の実鎖射から回収する。
方針：元の成分生成元の定義と、最高生成元像の次数移送・後合成の交換を使う。
規約：元の実 dg 関手と Hom 鎖射を保持。使われ方：標準面の削除成分の回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 成分は、元の濃度次元の Serre 生成射と実 dg Hom 射の最高生成元像。 -/
lemma cubicalLambdaNativeSimplexData_hom_normalized {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ)) :
    (cubicalLambdaNativeSimplexData A F).hom I a b k hI ha hb hk =
      eqToHom (congrArg (fun d => (homObject A D
        (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X d)
        (show -((I.card - 2 : ℕ) : ℤ) = k by omega))
        (serreCubeTopCellImage A _ (I.card - 2)
          (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
            F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))) := by
  subst a
  subst b
  subst k
  change (F.map _ _).f _ (simplexSubsetLambdaGenerator A I hI) = _
  unfold simplexSubsetLambdaGenerator
  exact serreCubeTopCellImage_cast_post A (I.card - 2) (2 - (I.card : ℤ)) (by omega)
    (simplexSubsetLambdaCell A I hI) (F.map _ _)

end SerrePositivity.KST.SConstruction
