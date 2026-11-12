module
public import SerrePositivity.KST.SConstruction.SimplexHABeadTailCells
public import SerrePositivity.KST.SConstruction.SimplexHAZeroChainRecovery

/-! # 零次元の元の二点部分集合生成射との一致
概要：零次元の生成元語の実鎖射と逆 HA 鎖射を、元の二点部分集合の実生成射へ戻す。
方針：右側一点の bead の実鎖射の式と、元の零次元逆鎖射の回収式を合成する。
規約：同じ端点と元の cube 次元移送を保持。使われ方：逆律の元の標準面への基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 零次元の元の生成元語の実鎖射は、同じ二点部分集合の元の実生成射。 -/
lemma simplexHAGeneratorWord_zero_cell {n : ℕ} (i : SerreCubeGeneratorIndex 0)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b)
    (hI : 2 ≤ ({v 0, b} : Finset (Fin (n + 1))).card)
    (hmin : v 0 = ({v 0, b} : Finset (Fin (n + 1))).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI))
    (hmax : b = ({v 0, b} : Finset (Fin (n + 1))).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI)) :
    simplexHABeadWordCell A (simplexHAGeneratorWord 0 i v b hb) =
      eqToHom (congrArg (serreCubeComplex A)
        (show 0 = ({v 0, b} : Finset (Fin (n + 1))).card - 2 by simp [ne_of_lt hb])) ≫
          simplexSubsetLambdaCellAt A {v 0, b} (v 0) b hI hmin hmax := by
  change simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail {b} (Finset.singleton_nonempty b)
    (v 0) (by intro t ht; simpa only [Finset.mem_singleton.mp ht] using hb)) = _
  have h := simplexHABeadTail_cell A {b} (Finset.singleton_nonempty b) (v 0)
    (by intro t ht; simpa only [Finset.mem_singleton.mp ht] using hb) hI hmin
    (by simpa only [Finset.max'_singleton] using hmax)
  exact h.trans (by rfl)

/-- 元の実 dg 関手からの零次元逆鎖射は、元の二点部分集合の実生成射の像を回収する。 -/
lemma simplexHAZeroChainLift_subset_recovery {D : Type v} [DGCategory A D] {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (v : Fin 1 ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v 0 < b)
    (hI : 2 ≤ ({v 0, b} : Finset (Fin (n + 1))).card)
    (hmin : v 0 = ({v 0, b} : Finset (Fin (n + 1))).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI))
    (hmax : b = ({v 0, b} : Finset (Fin (n + 1))).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI)) :
    simplexHAZeroChainLift A (cubicalLambdaNativeSimplex A F) v b hb =
      (eqToHom (congrArg (serreCubeComplex A)
        (show 0 = ({v 0, b} : Finset (Fin (n + 1))).card - 2 by simp [ne_of_lt hb])) ≫
          simplexSubsetLambdaCellAt A {v 0, b} (v 0) b hI hmin hmax) ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) := by
  exact (simplexHAZeroChainLift_recovery A F v b hb).trans
    (congrArg (fun f => f ≫ F.map _ _)
      (simplexHAGeneratorWord_zero_cell A PUnit.unit v b hb hI hmin hmax))

end SerrePositivity.KST.SConstruction
