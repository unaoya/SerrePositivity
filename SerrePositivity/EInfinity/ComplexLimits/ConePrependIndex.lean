module
public import SerrePositivity.EInfinity.ComplexLimits.ConeWithoutFirst
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：元の順序埋め込みに始点を加えた単射と、混合 cochain の添字の像を計算する。
方針：零と後続元に分け、元の単射性と後続元の単射性を使う。
規約：元の prependOrderHom を使う。使われ方：実 cone の単射 pullback 成分。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
open SerrePositivity.InfinityCategories

lemma prepend_injective {m n : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact False.elim ((Fin.succ_ne_zero (e j)) hij.symm)
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim ((Fin.succ_ne_zero (e i)) hij)
    | succ j => exact congrArg Fin.succ (e.injective (Fin.succ_injective _ hij))

lemma prepend_eq_zero_iff {m n : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (i : Fin (m + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i = 0 ↔ i = 0 := by
  constructor
  · exact fun h => prepend_injective e h
  · intro h
    subst i
    rfl

lemma withoutFirst_image_prepend {m n : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) :
    withoutFirst (I.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)) = (withoutFirst I).image e := by
  ext i
  simp only [withoutFirst, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    induction j using Fin.cases with
    | zero => exact False.elim ((Fin.succ_ne_zero i) hji.symm)
    | succ j => exact ⟨j, hj, Fin.succ_injective _ hji⟩
  · rintro ⟨j, hj, he⟩
    refine ⟨j.succ, hj, ?_⟩
    change (e j).succ = i.succ
    rw [he]

lemma zero_mem_image_prepend {m n : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) :
    0 ∈ I.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) ↔ 0 ∈ I := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact (prepend_eq_zero_iff e i).mp he ▸ hi
  · exact fun h => Finset.mem_image.mpr ⟨0, h, rfl⟩

end SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
