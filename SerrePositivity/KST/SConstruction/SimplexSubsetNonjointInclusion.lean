module
public import SerrePositivity.KST.SConstruction.SimplexSubsetInclusionCoordinates

/-! # 元の部分集合包含の非 joint 頂点の順序埋め込み
概要：元の同端点の包含は内部頂点の順序を保ち、その像は元の小さい集合に属する頂点。
方針：元の端点と局所番号の単射性で非 joint 性を示し、元の昇順列挙で像を判定する。
規約：元の頂点添字を保持。使われ方：右端からの数値座標の順序と像。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の部分集合の昇順列挙は、元の頂点の厳密な順序を保つ。 -/
lemma simplexSubsetOrder_strictMono {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    StrictMono (simplexSubsetOrder I hI) :=
  (I.orderEmbOfFin (show I.card = I.card - 1 + 1 by omega)).strictMono

/-- 元の非 joint 局所頂点の像は、同じ最小・最大元の厳密な内部にある。 -/
lemma simplexSubsetNonjoint_bounds {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (v : (NecklaceShape.single (I.card - 1)).NonjointVertex) :
    I.min' (simplexSubsetNonempty I hI) < simplexSubsetOrder I hI v.val ∧
      simplexSubsetOrder I hI v.val < I.max' (simplexSubsetNonempty I hI) := by
  have hv : v.val.val ≠ 0 ∧ v.val.val ≠ I.card - 1 := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton, not_or]
      using v.property
  have hvb : v.val.val < I.card - 1 + 1 := v.val.isLt
  exact ⟨(simplexSubsetOrder_first I hI).symm.trans_lt
    (simplexSubsetOrder_strictMono I hI (show (0 : Fin (I.card - 1 + 1)) < v.val by
      change 0 < v.val.val; omega)),
    (simplexSubsetOrder_strictMono I hI (show v.val < Fin.last (I.card - 1) by
      change v.val.val < I.card - 1; omega)).trans_eq (simplexSubsetOrder_last I hI)⟩

variable {n : ℕ} (I J : Finset (Fin (n + 1)))
  (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
  (hmin : I.min' (simplexSubsetNonempty I hI) = J.min' (simplexSubsetNonempty J hJ))
  (hmax : I.max' (simplexSubsetNonempty I hI) = J.max' (simplexSubsetNonempty J hJ))

/-- 元の部分集合包含は、元の非 joint 頂点の順序埋め込みを与える。 -/
def simplexSubsetNonjointInclusion :
    (NecklaceShape.single (I.card - 1)).NonjointVertex ↪o
      (NecklaceShape.single (J.card - 1)).NonjointVertex where
  toFun v := ⟨simplexSubsetInclusionOrder I J hI hJ hIJ v.val, by
    intro h
    simp only [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · have he := simplexSubsetInclusionOrder_injective I J hI hJ hIJ
        ((Fin.ext h).trans (simplexSubsetInclusionOrder_first I J hI hJ hIJ hmin).symm)
      exact v.property ((congrArg (fun w => w.val ∈ (NecklaceShape.single (I.card - 1)).joints)
        he).mpr (NecklaceShape.single (I.card - 1)).zero_mem)
    · have he := simplexSubsetInclusionOrder_injective I J hI hJ hIJ
        ((Fin.ext h).trans (simplexSubsetInclusionOrder_last I J hI hJ hIJ hmax).symm)
      exact v.property ((congrArg (fun w => w.val ∈ (NecklaceShape.single (I.card - 1)).joints)
        he).mpr (NecklaceShape.single (I.card - 1)).last_mem)⟩
  inj' v w h := Subtype.ext (simplexSubsetInclusionOrder_injective I J hI hJ hIJ
    (congrArg Subtype.val h))
  map_rel_iff' := by
    intro v w
    exact ((simplexSubsetInclusionOrder I J hI hJ hIJ).monotone.strictMono_of_injective
      (simplexSubsetInclusionOrder_injective I J hI hJ hIJ)).le_iff_le

/-- 元の非 joint 包含も、元の昇順列挙で同じ頂点を回収する。 -/
lemma simplexSubsetNonjointInclusion_recovery
    (v : (NecklaceShape.single (I.card - 1)).NonjointVertex) :
    simplexSubsetOrder J hJ (simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax v).val =
      simplexSubsetOrder I hI v.val := simplexSubsetInclusionOrder_recovery I J hI hJ hIJ v.val

/-- 元の非 joint 包含の像は、元の小さい部分集合に属する同じ内部頂点の全体。 -/
lemma simplexSubsetNonjointInclusion_range :
    Set.range (simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax) =
      {w | simplexSubsetOrder J hJ w.val ∈ I} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    change simplexSubsetOrder J hJ
      (simplexSubsetNonjointInclusion I J hI hJ hIJ hmin hmax v).val ∈ I
    exact (congrArg (fun j => j ∈ I)
      (simplexSubsetNonjointInclusion_recovery I J hI hJ hIJ hmin hmax v)).mpr
        (simplexSubsetOrder_mem I hI v.val)
  · intro hw
    let j := simplexSubsetOrder J hJ w.val
    have hb := simplexSubsetNonjoint_bounds J hJ w
    let v := simplexSubsetInteriorVertex I hI j hw (hmin.trans_lt hb.1) (hb.2.trans_eq hmax.symm)
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply simplexSubsetOrder_injective J hJ
    exact (simplexSubsetNonjointInclusion_recovery I J hI hJ hIJ hmin hmax v).trans
      (simplexSubsetVertexIndex_recovery I hI j hw)

end SerrePositivity.KST.SConstruction
