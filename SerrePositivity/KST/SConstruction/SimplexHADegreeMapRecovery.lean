module
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorMapRecovery
public import SerrePositivity.KST.SConstruction.SimplexHADegreeLift

/-! # 元の native HA 次数線形復元による実 dg 関手の回収
概要：全生成元の実像を比較し、元の部分集合生成射の像を全整数次数で回収する。
方針：指定次数への移送と元の全生成元判定で、実鎖射の次数成分へ戻す。
規約：元の実 dg 関手と復元を保持。使われ方：逆 Hom 射の左逆と単体作用素比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実 dg 関手からの native HA 線形復元は、元の実像の全整数次数成分を回収する。 -/
lemma simplexHADegreeLift_map_recovery {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last m) < b) (k : ℤ) :
    simplexHADegreeLift A (cubicalLambdaNativeSimplexData A F) m v b hb k =
      (simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫
          F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).f k := by
  apply serreCube_degree_hom_ext A m k
  intro i hi
  let c := simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) ≫ F.map _ _
  exact (simplexHADegreeLift_generator A (cubicalLambdaNativeSimplexData A F)
    m v b hb k i hi).trans
      ((congrArg (fun w => eqToHom (congrArg (fun d => (homObject A D
        (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X d) hi) w)
          (simplexHAGeneratorValue_map_recovery A F m i v b hb)).trans
            (complexMap_degree_cast A c hi (serreCubeGenerator A m i)).symm)

end SerrePositivity.KST.SConstruction
