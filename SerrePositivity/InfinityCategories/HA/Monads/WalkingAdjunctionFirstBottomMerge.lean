module

public import Mathlib.Data.Finset.Max
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergePositions

/-!
概要：非退化な実全単体に存在する併合の位置から最小の位置を実際に選ぶ。
方針：証明済みの非空の有限部分集合の最小元を取る。
規約：位置の存在や最小性を仮定しない。
使われ方：Riehl–Verity §4.1–§4.2の原子の最初の併合の選択、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最小の併合の位置と、その実条件・最小性の実証明。
方針：実条件を満たす有限部分集合の最小元を構成する。
規約：非空性は元の非退化性から証明する。使われ方：Riehl–Verity §4.1の最初の折り返し。 -/
def walkingAdjunctionFirstBottomMergeData {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    {k : Fin (n + 1) // WalkingAdjunctionBottomMergeAt H k ∧
      ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j} := by
  classical
  let s := Finset.univ.filter (WalkingAdjunctionBottomMergeAt H)
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := walkingAdjunctionExists_bottom_merge H hlast hnd
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, ?_⟩
  intro j hj
  exact Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

/-- 概要：最初の併合の実位置。
方針：構成した最小元から取り出す。規約：元の辺の有限添字。
使われ方：Riehl–Verity §4.1の実細分を挿入する場所。 -/
def walkingAdjunctionFirstBottomMergeIndex {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    Fin (n + 1) := (walkingAdjunctionFirstBottomMergeData H hlast hnd).val

/-- 概要：選んだ実位置で元の実射は二番目の点を0へ送る。
方針：構成した有限最小元の所属を使う。規約：条件を仮定として追加しない。
使われ方：Riehl–Verity §4.1の実併合と実残余射の構成。 -/
lemma walkingAdjunctionFirstBottomMergeIndex_spec {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    WalkingAdjunctionBottomMergeAt H (walkingAdjunctionFirstBottomMergeIndex H hlast hnd) :=
  (walkingAdjunctionFirstBottomMergeData H hlast hnd).property.1

/-- 概要：選んだ実位置は他の全ての併合の位置以下。
方針：構成した有限最小元の最小性を使う。規約：全辺の比較。
使われ方：Riehl–Verity §4.1の最初の折り返しの検収。 -/
lemma walkingAdjunctionFirstBottomMergeIndex_minimal {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    {j : Fin (n + 1)} (hj : WalkingAdjunctionBottomMergeAt H j) :
    walkingAdjunctionFirstBottomMergeIndex H hlast hnd ≤ j :=
  (walkingAdjunctionFirstBottomMergeData H hlast hnd).property.2 j hj

end SerrePositivity.InfinityCategories.HA.Monads
