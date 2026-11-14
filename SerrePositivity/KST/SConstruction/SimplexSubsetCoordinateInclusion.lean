module
public import SerrePositivity.KST.SConstruction.SimplexSubsetNonjointInclusion
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceNumericMap

/-! # 元の部分集合包含の右端からの数値座標埋め込み
概要：元の非 joint 包含を右端からの列挙で数値化し、元の順序・像・入力値を回収する。
方針：元の二つの反順列挙の間に、元の非 joint 頂点の順序埋め込みを挟む。
規約：座標零は元の右端。使われ方：内部点削除の標準零面の同定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (I J : Finset (Fin (n + 1)))
  (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
  (hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
  (hmax : I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))

/-- 元の部分集合包含の、元の右端からの数値座標間の関数。 -/
def simplexSubsetCoordinateInclusionFun :
    Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension →
      Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).dimension :=
  fun i => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate.symm
    (simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i))

/-- 元の数値座標は、元の非 joint 包含の同じ頂点像を回収する。 -/
lemma simplexSubsetCoordinateInclusion_recovery
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate
        (simplexSubsetCoordinateInclusionFun I J hI hJ hIJ hmin hmax i) =
      simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate.apply_symm_apply _

/-- 元の右端からの数値座標の包含は、元の数値順序を厳密に保つ。 -/
lemma simplexSubsetCoordinateInclusion_strictMono :
    StrictMono (simplexSubsetCoordinateInclusionFun I J hI hJ hIJ hmin hmax) := by
  intro i j hij
  apply ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate_lt _ _).mp
  rw [simplexSubsetCoordinateInclusion_recovery, simplexSubsetCoordinateInclusion_recovery]
  exact (simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax).strictMono
    (((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate_lt j i).mpr hij)

/-- 元の右端からの全数値座標間の、同じ元の順序埋め込み。 -/
def simplexSubsetCoordinateInclusion :
    Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension ↪o
      Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).dimension :=
  OrderEmbedding.ofStrictMono (simplexSubsetCoordinateInclusionFun I J hI hJ hIJ hmin hmax)
    (simplexSubsetCoordinateInclusion_strictMono I J hI hJ hIJ hmin hmax)

/-- 元の数値座標の包含の像は、元の小さい部分集合に属する同じ内部頂点の座標全体。 -/
lemma simplexSubsetCoordinateInclusion_range :
    Set.range (simplexSubsetCoordinateInclusion I J hI hJ hIJ hmin hmax) =
      {j | _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate j).val ∈ I} := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate
      (simplexSubsetCoordinateInclusionFun I J hI hJ hIJ hmin hmax i)).val ∈ I
    have h := (congrArg (fun v => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ v.val)
      (simplexSubsetCoordinateInclusion_recovery I J hI hJ hIJ hmin hmax i)).trans
        (simplexSubsetNonjointInclusion_recovery I J hI hJ hIJ hmin hmax _)
    exact (congrArg (fun v => v ∈ I) h).mpr (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI _)
  · intro hj
    have h := (Set.ext_iff.mp (simplexSubsetNonjointInclusion_range I J hI hJ hIJ hmin hmax)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate j)).mpr hj
    obtain ⟨v, hv⟩ := h
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.symm v, ?_⟩
    apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate.injective
    exact (simplexSubsetCoordinateInclusion_recovery I J hI hJ hIJ hmin hmax _).trans
      ((congrArg (simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax)
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.apply_symm_apply v)).trans hv)

/-- 元の数値座標の包含の像では、元の実 cube 射が同じ元の入力値を回収する。 -/
lemma simplexSubsetCoordinateInclusion_numeric
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax) x
      (simplexSubsetCoordinateInclusion I J hI hJ hIJ hmin hmax i) = x i := by
  have h := necklaceBooleanMap_nonjoint_of_injective
    (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax)
    (necklaceSimplexSubsetInclusion_vertex_injective I J hI hJ hIJ hmin hmax)
    (fun v => x ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.symm v))
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate i)
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (J.card - 1)).nonjointCoordinate
      (simplexSubsetCoordinateInclusion I J hI hJ hIJ hmin hmax i))
    (congrArg Subtype.val
      (simplexSubsetCoordinateInclusion_recovery I J hI hJ hIJ hmin hmax i)).symm
  exact h.trans (congrArg x
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).nonjointCoordinate.symm_apply_apply i))

end SerrePositivity.KST.SConstruction
