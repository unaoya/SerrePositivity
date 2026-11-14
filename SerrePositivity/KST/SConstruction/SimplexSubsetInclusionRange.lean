module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexSubsetInclusionOrder
public import SerrePositivity.KST.SConstruction.SimplexSubsetVertexIndex
public import SerrePositivity.KST.SConstruction.SimplexSubsetNonjointInclusion

/-! # 元の部分集合包含の全局所頂点の像
概要：元の昇順包含の像を、同じ大きい部分集合の局所頂点が小さい集合に属する条件で判定。
方針：元の昇順列挙の逆で、元の包含の全ての像を回収する。
規約：全頂点と元の所属を保持。使われ方：左右フィルターの局所始端・終端ブロック。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の部分集合包含の全局所頂点像は、元の小さい部分集合に属する局所頂点の全体。 -/
lemma simplexSubsetInclusionOrder_range {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ) =
      {v | _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ v ∈ I} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ w) ∈ I
    exact (congrArg (fun j => j ∈ I)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ w)).mpr (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI w)
  · intro hv
    refine ⟨simplexSubsetVertexIndex I hI (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ v) hv, ?_⟩
    apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective J hJ
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ _).trans
      (simplexSubsetVertexIndex_recovery I hI (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ v) hv)

end SerrePositivity.KST.SConstruction
