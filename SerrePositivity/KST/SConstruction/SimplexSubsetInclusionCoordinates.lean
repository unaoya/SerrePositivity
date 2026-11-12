module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetInclusion
public import SerrePositivity.KST.SConstruction.SimplexSubsetVertexIndex
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceBooleanMap

/-! # 元の部分集合包含の全内部頂点座標
概要：元の部分集合包含の cube 作用は、欠けた内部頂点で零、残った内部頂点で元の値。
方針：元の頂点像の単射性と、元の Bool 作用の全ファイバー表示を使う。
規約：元の内部頂点そのものを添字にする。使われ方：内部点削除の零面の同定。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の単射な頂点作用の像の非 joint 座標では、元の同じ非 joint 入力値を回収する。 -/
lemma necklaceBooleanMap_nonjoint_of_injective {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U)
    (hf : Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f)) (x : T.down.NonjointVertex → Bool)
    (v : T.down.NonjointVertex) (w : U.down.NonjointVertex)
    (hw : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f v.val = w.val) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f x w = x v := by
  apply Bool.eq_iff_iff.mpr
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    have hjv : j = v.val := hf (he.trans hw.symm)
    subst j
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_right v.property] using hj
  · intro hv
    exact ⟨v.val, by
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeFullBits, dite_eq_right v.property] using hv, hw⟩

variable {n : ℕ} (I J : Finset (Fin (n + 1)))
  (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
  (hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
  (hmax : I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))

/-- 元の包含に欠ける内部頂点の出力座標は、元の全入力に対して零。 -/
lemma simplexSubsetInclusion_coordinate_missing
    (x : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).NonjointVertex → Bool)
    (j : Fin (n + 1)) (hj : j ∈ J) (hjI : j ∉ I)
    (hjm : J.min' (Finset.card_pos.mp (by omega)) < j)
    (hjM : j < J.max' (Finset.card_pos.mp (by omega))) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax) x
      (simplexSubsetInteriorVertex J hJ j hj hjm hjM) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨v, _, he⟩ := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff _ _ _).mp h
  have hvertex := congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ) he
  have hvj : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v = j :=
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ v).symm.trans
      (hvertex.trans (simplexSubsetVertexIndex_recovery J hJ j hj))
  exact hjI (hvj ▸ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI v)

/-- 元の包含に残る内部頂点の出力座標は、元の同じ頂点の入力座標そのもの。 -/
lemma simplexSubsetInclusion_coordinate_retained
    (x : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).NonjointVertex → Bool)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (Finset.card_pos.mp (by omega)) < j)
    (hjM : j < I.max' (Finset.card_pos.mp (by omega))) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax) x
        (simplexSubsetInteriorVertex J hJ j (hIJ hj) (hmin.symm.trans_lt hjm) (hjM.trans_eq hmax)) =
      x (simplexSubsetInteriorVertex I hI j hj hjm hjM) := by
  apply necklaceBooleanMap_nonjoint_of_injective _
    (necklaceSimplexSubsetInclusion_vertex_injective I J hI hJ hIJ hmin hmax)
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective J hJ
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ _).trans
    ((simplexSubsetVertexIndex_recovery I hI j hj).trans
      (simplexSubsetVertexIndex_recovery J hJ j (hIJ hj)).symm)

end SerrePositivity.KST.SConstruction
