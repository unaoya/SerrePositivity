module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExExpansionSmallComplexity
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.IsUniquelyCodimOneFace

/-!
# Ex pairing の指定面の一意性

概要：非退化で前段の対応先でない単体へ戻る面は指定した面だけである。
方針：前側の面の複雑度の減少と、後ろの面の型 I または退化という二択を使う。
規約：Moss 2020 Lemma 29 の指定面の一意性。
使われ方：Mathlib の proper pairing の条件。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：前側の面は最小閾値が正の元の単体に等しくない。
方針：等しければ元の単体の複雑度が一つ小さい閾値以下となる。
規約：Moss 2020 Lemma 29、前側の面。
使われ方：指定面以外の面の除外。
-/
theorem exExpansion_front_ne_source (X : SSet.{u}) (n : ℕ) (h : Fin (n + 1))
    (i : Fin (n + 3)) (hi : i ≤ h.succ.castSucc) (s : (SSet.ex.obj X) _⦋n + 1⦌)
    (hs : exComplexityLevel X ⦋n + 1⦌ s = h.succ) :
    (SSet.ex.obj X).δ i (exExpansion X (n + 1) h.succ s) ≠ s := by
  intro he
  have hm : s ∈ exComplexity X ⦋n + 1⦌ h.succ := hs ▸ exComplexityLevel_mem X _ s
  have hl := exExpansion_front_complexity X n h i hi s hm
  rw [he] at hl
  have hle := (exComplexityLevel_le_iff X ⦋n + 1⦌ s h.castSucc).mpr hl
  rw [hs] at hle
  have hv : h.val + 1 ≤ h.val := hle
  omega

/--
概要：後ろの面は、非退化で前段の対応先でない元の単体に等しくない。
方針：面の拡張の閾値が最小なら前段の像となり、小さくできれば退化する。
規約：Moss 2020 Lemma 29、後ろの面。
使われ方：指定面以外の面の除外。
-/
theorem exExpansion_rear_ne_source (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (j : Fin (n + 2)) (hkj : k.castSucc < j) (s : (SSet.ex.obj X) _⦋n + 1⦌)
    (hs : exComplexityLevel X ⦋n + 1⦌ s = k.castSucc)
    (hnd : s ∈ (SSet.ex.obj X).nonDegenerate (n + 1))
    (him : s ∉ Set.range (exPairingStep X n)) :
    (SSet.ex.obj X).δ j.succ (exExpansion X (n + 1) k.castSucc s) ≠ s := by
  intro he
  rw [exExpansion_rear_face X n k j hkj s] at he
  let t := (SSet.ex.obj X).δ j s
  have hm : s ∈ exComplexity X ⦋n + 1⦌ k.castSucc := hs ▸ exComplexityLevel_mem X _ s
  have ht : t ∈ exComplexity X ⦋n⦌ k := exComplexity_face X n k j s hm
  have hl := (exComplexityLevel_le_iff X ⦋n⦌ t k).mpr ht
  rcases lt_or_eq_of_le hl with hlt | heq
  · have hd := exExpansion_degenerate_of_complexity_lt X n _ k hlt t
      (exComplexityLevel_mem X _ t)
    rw [show exExpansion X n k t = s from he] at hd
    exact ((SSet.ex.obj X).mem_nonDegenerate_iff_notMem_degenerate s).mp hnd hd
  · apply him
    refine ⟨t, ?_⟩
    change exExpansion X n (exComplexityLevel X ⦋n⦌ t) t = s
    rw [heq]
    exact he

/--
概要：正次元の型 II の単体について、対応先から元へ戻る面の添字は一意である。
方針：指定面より前と後をそれぞれ除外し、指定面は復元則で確認する。
規約：Moss 2020 Lemma 29。型 II の条件は明示的な三つの仮定で表す。
使われ方：proper pairing への接続。
-/
theorem exPairingStep_face_unique_succ (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n + 1⦌)
    (hnd : s ∈ (SSet.ex.obj X).nonDegenerate (n + 1))
    (hu : s ∉ Set.range ((exUnitAt X).app (op ⦋n + 1⦌)))
    (him : s ∉ Set.range (exPairingStep X n)) :
    ∃! i : Fin (n + 3), (SSet.ex.obj X).δ i (exPairingStep X (n + 1) s) = s := by
  let k := exComplexityLevel X ⦋n + 1⦌ s
  have hk : k ≠ 0 := fun h => hu ((exComplexityLevel_zero_iff X _ s).mp h)
  refine ⟨k.succ, exExpansion_face X (n + 1) k s, ?_⟩
  intro i hi
  change (SSet.ex.obj X).δ i (exExpansion X (n + 1) k s) = s at hi
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let h := k.pred hk
    have he : h.succ = k := Fin.succ_pred k hk
    have hi' : i ≤ h.succ.castSucc := by
      rw [he]
      change i.val ≤ k.val
      have hv : i.val < k.val + 1 := hlt
      omega
    exact exExpansion_front_ne_source X n h i hi' s he.symm (by simpa only [he] using hi)
  · have hkl : k ≠ Fin.last (n + 1) := by
      intro he
      have hv := i.isLt
      have hg : k.val + 1 < i.val := hgt
      simp only [he, Fin.val_last] at hg
      omega
    let l := k.castPred hkl
    have hl : l.castSucc = k := Fin.castSucc_castPred k hkl
    have hiz : i ≠ 0 := ne_of_gt ((Fin.zero_le k.succ).trans_lt hgt)
    let j := i.pred hiz
    have hj : j.succ = i := Fin.succ_pred i hiz
    have hkj : l.castSucc < j := by
      rw [hl]
      change k.val < i.val - 1
      have hg : k.val + 1 < i.val := hgt
      omega
    exact exExpansion_rear_ne_source X n l j hkj s hl.symm hnd him
      (by simpa only [hl, hj] using hi)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
