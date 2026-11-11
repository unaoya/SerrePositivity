module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeSimplexData
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageTransport

/-! # 元の部分集合実生成射からの native 成分の回収
概要：元の HA 成分を、同じ部分集合の実 Serre 鎖射の最高生成元像で回収する。
方針：元の生成元の定義と、元の指定次数移送・dg Hom 鎖射の可換性を使う。
規約：元の部分集合、次数、端点を保持。使われ方：連結語評価の基底となる回収式。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native 成分は、元の実部分集合生成射の最高生成元像の指定次数移送。 -/
lemma cubicalLambdaNativeSimplexData_hom_cell {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Finset.card_pos.mp (by omega)))
    (hb : b = I.max' (Finset.card_pos.mp (by omega))) (hk : k = 2 - (I.card : ℤ)) :
    (cubicalLambdaNativeSimplexData A F).hom I a b k hI ha hb hk =
      eqToHom (congrArg (fun d => (homObject A D
        (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X d)
        (show -((I.card - 2 : ℕ) : ℤ) = k by omega))
        (serreCubeTopCellImage A _ (I.card - 2)
          (by
            subst a b
            exact simplexSubsetLambdaCell A I hI ≫ F.map _ _)) := by
  subst a b k
  change (F.map _ _).f _ (simplexSubsetLambdaGenerator A I hI) = _
  unfold simplexSubsetLambdaGenerator
  exact serreCubeTopCellImage_cast_post A _ _ (by omega) _ _

end SerrePositivity.KST.SConstruction
