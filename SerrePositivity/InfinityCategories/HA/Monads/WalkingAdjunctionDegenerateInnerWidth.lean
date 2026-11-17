module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthInnerFace
public import SerrePositivity.InfinityCategories.HA.Monads.NerveDegeneracyEdges

/-!
概要：非退化な実全鎖の内側面が退化すれば、その幅は真に小さくなる。
方針：残る実辺は非同型なので、退化は合成辺の同型性に限られることを実際に示す。
規約：原子性や指定した最初の位置を使わない。
使われ方：Riehl–Verity Proposition 4.2.15の退化面の順序づけ、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：非退化な実全鎖の内側面は、合成辺が非同型であることと同値に非退化。
方針：他の全実辺は元の非同型辺へ戻し、指定辺は実合成辺へ輸送する。
規約：四つの元のHomを扱う。使われ方：Riehl–Verity §4.2の実退化面の判定。 -/
lemma walkingAdjunctionInnerFace_nondegenerate_iff_not_isIso {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (k : Fin (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2)) :
    (ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) ↔
    ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      H.map (homOfLE (Fin.castSucc_le_succ k.succ))) := by
  let F := finiteChainFace H k.succ.castSucc
  have hs := finiteChainFace_inner_before_obj H k k.castSucc (show k.val ≤ k.val from le_rfl)
  have ht := finiteChainFace_inner_after_obj H k k.succ
    (show k.val < k.val + 1 from Nat.lt_succ_self _)
  have he := finiteChainFace_inner_merged_edge H k
  constructor
  · intro hf hi
    have := hi
    have h := (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso F).mp hf k
    exact h (isIso_of_equal_objects_hom_heq hs.symm ht.symm _ _ he.symm)
  · intro hc
    have hp := (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd
    apply (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso F).mpr
    intro j hj
    have := hj
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · apply hp j.castSucc
      exact isIso_of_equal_objects_hom_heq
        (finiteChainFace_inner_before_obj H k j.castSucc hlt.le)
        (finiteChainFace_inner_before_obj H k j.succ (by
          change j.val + 1 ≤ k.val
          exact hlt)) _ _ (finiteChainFace_inner_before_edge H k j hlt)
    · exact hc (isIso_of_equal_objects_hom_heq hs ht _ _ he)
    · apply hp j.succ
      exact isIso_of_equal_objects_hom_heq
        (finiteChainFace_inner_after_obj H k j.castSucc hgt)
        (finiteChainFace_inner_after_obj H k j.succ (by
          change k.val < j.val + 1
          exact lt_trans hgt (Nat.lt_succ_self _))) _ _
        (finiteChainFace_inner_after_edge H k j hgt)

/-- 概要：非退化な実全鎖の内側面が退化なら、その有限順序の幅は元より真に小さい。
方針：合成辺の同型性で変化量を0にし、元の非同型辺の正値と実幅の欠損の式を使う。
規約：面や元の原子性を仮定しない。使われ方：Riehl–Verity §4.2の幅による厳密な減少。 -/
lemma walkingAdjunctionOrdinalWidth_inner_lt_of_not_nondegenerate {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (k : Fin (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2))
    (hf : ULift.up (finiteChainFace H k.succ.castSucc) ∉
      (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) <
      walkingAdjunctionOrdinalWidth H := by
  have hc : IsIso (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      H.map (homOfLE (Fin.castSucc_le_succ k.succ))) := by
    by_contra hn
    exact hf ((walkingAdjunctionInnerFace_nondegenerate_iff_not_isIso H k hnd).mpr hn)
  have hv := (walkingAdjunctionMapVariation_zero_iff_isIso _).mpr hc
  have hp := walkingAdjunctionMapVariation_pos_of_not_isIso _
    ((walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd k.castSucc)
  apply walkingAdjunctionOrdinalWidth_inner_lt H k
  omega

end SerrePositivity.InfinityCategories.HA.Monads
