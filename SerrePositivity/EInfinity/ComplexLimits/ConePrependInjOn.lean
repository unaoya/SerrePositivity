module
public import SerrePositivity.EInfinity.ComplexLimits.ConePrependIndex

/-!
概要：始点を前置した任意の単調写像の集合上の単射性を、元の尾の単射性へ戻す。
方針：零と後続元の像が交わらないことを使い、後続元どうしを比較する。
規約：全射・単射の全域仮定を置かない。使われ方：実 cone の全退化混合成分。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
open SerrePositivity.InfinityCategories

lemma prepend_injOn_iff {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 2))) :
    Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ) (I : Set (Fin (m + 2))) ↔
      Set.InjOn θ ((withoutFirst I) : Set (Fin (m + 1))) := by
  constructor
  · intro h i hi j hj hij
    have hi' : i.succ ∈ I := (Finset.mem_filter.mp hi).2
    have hj' : j.succ ∈ I := (Finset.mem_filter.mp hj).2
    exact Fin.succ_injective _ (h hi' hj' (congrArg Fin.succ hij))
  · intro h i hi j hj hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact False.elim ((Fin.succ_ne_zero (θ j)) hij.symm)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact False.elim ((Fin.succ_ne_zero (θ i)) hij)
      | succ j =>
        apply congrArg Fin.succ
        apply h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
        exact Fin.succ_injective _ hij

lemma withoutFirst_image_prepend_map {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 2))) :
    withoutFirst (I.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ)) = (withoutFirst I).image θ := by
  ext i
  simp only [withoutFirst, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    induction j using Fin.cases with
    | zero => exact False.elim ((Fin.succ_ne_zero i) hji.symm)
    | succ j => exact ⟨j, hj, Fin.succ_injective _ hji⟩
  · rintro ⟨j, hj, he⟩
    refine ⟨j.succ, hj, ?_⟩
    change (θ j).succ = i.succ
    rw [he]

end SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
