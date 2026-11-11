module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadTail
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWordReindex
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces

/-! # 元の全 tensor 生成元の部分集合 bead 連結語への読み替え
概要：零端点は削除、一端点は切断、辺は同じ bead の内部頂点として読む。
方針：元の最右座標から処理し、未処理の右側頂点集合を保持して帰納する。
規約：元の頂点順と自由次元を保持。使われ方：HA 成分の全生成元への値の指定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の零・一端点と辺を、同じ頂点順・自由次元を持つ正長 bead の連結語へ読む。 -/
def simplexHABeadWordDecode {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (v 0) (T.max' hT)
      (serreCubeGeneratorFreeDimension m i + T.card - 1) := by
  induction m generalizing T with
  | zero =>
    exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex rfl
      (by simp only [serreCubeGeneratorFreeDimension, zero_add])
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)
  | succ m ih =>
    obtain ⟨i, j⟩ := i
    let vp : Fin (m + 1) ↪o Fin (n + 1) := Fin.castSuccOrderEmb.trans v
    let r := v (Fin.last (m + 1))
    have hr : vp (Fin.last m) < r := v.strictMono (by
      change (Fin.last m).castSucc < Fin.last (m + 1)
      exact Fin.castSucc_lt_last _)
    have hbp : ∀ t ∈ T, vp (Fin.last m) < t := fun t ht => hr.trans (hb t ht)
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_)) j
    · exact ih i vp T hT hbp
    · have hbr : ∀ t ∈ ({r} : Finset (Fin (n + 1))), vp (Fin.last m) < t := by
        intro t ht
        simpa only [Finset.mem_singleton.mp ht] using hr
      have left := ih i vp {r} (Finset.singleton_nonempty r) hbr
      have hl : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (v 0) r (serreCubeGeneratorFreeDimension m i) := by
        change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (vp 0) r (serreCubeGeneratorFreeDimension m i)
        simpa only [Finset.card_singleton, Nat.add_sub_cancel, Finset.max'_singleton] using left
      change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (v 0) (T.max' hT)
        (serreCubeGeneratorFreeDimension m i + T.card - 1)
      have he : serreCubeGeneratorFreeDimension m i + (T.card - 1) =
          serreCubeGeneratorFreeDimension m i + T.card - 1 := by
        have hp := Finset.card_pos.mpr hT
        omega
      exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex rfl he (.join hl (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT r hb))
    · have hbi : ∀ t ∈ insert r T, vp (Fin.last m) < t := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hr
        · exact hbp t ht
      have hi := ih i vp (insert r T) (Finset.insert_nonempty r T) hbi
      have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T r hb
      change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (vp 0) (T.max' hT)
        (serreCubeGeneratorFreeDimension m i + 1 + T.card - 1)
      exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT r hb) (by
        have hc := Finset.card_insert_of_notMem hn
        omega) hi

end SerrePositivity.KST.SConstruction
