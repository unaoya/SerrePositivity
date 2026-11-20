module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexSubsetOrder
public import Mathlib.Order.Hom.Set

/-! # 元の単射な像部分集合の昇順列挙
概要：部分集合上で単射な元の単調写像は、元の昇順列挙を同じ番号の像列挙へ送る。
方針：元の像の濃度を保持し、同じ有限像を持つ厳密単調な二列の一意性を使う。
規約：元の全頂点番号と濃度移送を保持。使われ方：native HA の単射分岐の自然性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の単調写像が部分集合上単射なら、元の全列挙の像は同じ濃度の昇順像列挙。 -/
lemma simplexSubsetOrder_image_inj {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card)
    (hi : Set.InjOn α (I : Set (Fin (M + 1)))) (hJ : 2 ≤ (I.image α).card)
    (v : Fin (I.card - 1 + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ
      (Fin.cast (congrArg (fun d => d - 1 + 1) (Finset.card_image_of_injOn hi).symm) v) =
      α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v) := by
  let hlen := congrArg (fun d => d - 1 + 1) (Finset.card_image_of_injOn hi).symm
  let f : Fin (I.card - 1 + 1) → Fin (N + 1) :=
    fun i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ (Fin.cast hlen i)
  let g : Fin (I.card - 1 + 1) → Fin (N + 1) := fun i => α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI i)
  have hf : StrictMono f :=
    ((I.image α).orderEmbOfFin (show (I.image α).card =
      (I.image α).card - 1 + 1 by omega)).strictMono.comp (Fin.castOrderIso hlen).strictMono
  have hg : StrictMono g := by
    intro i j hij
    exact (α.monotone.monotoneOn (I : Set (Fin (M + 1)))).strictMonoOn_of_injOn hi
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI i) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI j)
      ((I.orderEmbOfFin (show I.card = I.card - 1 + 1 by omega)).strictMono hij)
  have hr : Set.range g = (I.image α : Set (Fin (N + 1))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨_, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI i, rfl⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      have hy' : y ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI) :=
        (Set.ext_iff.mp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_range I hI) y).mpr hy
      obtain ⟨i, rfl⟩ := hy'
      exact ⟨i, hxy⟩
  have hl : Set.range f = (I.image α : Set (Fin (N + 1))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem (I.image α) hJ _
    · intro hx
      have hx' : x ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ) :=
        (Set.ext_iff.mp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_range (I.image α) hJ) x).mpr hx
      obtain ⟨i, hi⟩ := hx'
      refine ⟨Fin.cast hlen.symm i, ?_⟩
      exact (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ) (Fin.ext rfl)).trans hi
  exact congrFun (hf.eq_of_range_eq hg (hl.trans hr.symm)) v

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
