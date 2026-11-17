module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowLastFace

/-!
概要：元の全実鎖に任意の面を取ると、有限順序の幅は増えない。
方針：先頭の面・最初の二辺の合成・尾部への再帰と実挿入の幅の式を使う。
規約：境界の面と空の実対象も含む。文字列の幅との全比較は別に行う。
使われ方：Riehl–Verity Proposition 4.2.15の実面とfiltration、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実幅の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：一点の実全鎖の有限順序の幅は、その実点の個数の二倍から補正を除いたもの。
方針：幅の定義で辺の有限和が空であることを使う。
規約：実対象が空の場合も含む。使われ方：Riehl–Verity §4.2の境界の実面。 -/
lemma walkingAdjunctionOrdinalWidth_zero {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) 0) :
    walkingAdjunctionOrdinalWidth H =
      walkingAdjunctionOrdinalCard X Y (H.obj 0) + walkingAdjunctionOrdinalCard X Y (H.obj 0) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) := by
  simp only [walkingAdjunctionOrdinalWidth, Fin.sum_univ_zero, Fin.last_zero, add_zero]

/-- 概要：一辺の実全鎖の有限順序の幅を、両端と実辺の変化量で表示する。
方針：幅の有限和を一点で評価する。規約：実射の全作用から計算する。
使われ方：Riehl–Verity §4.2の一辺の境界の比較。 -/
lemma walkingAdjunctionOrdinalWidth_one {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) 1) :
    walkingAdjunctionOrdinalWidth H = walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      walkingAdjunctionOrdinalCard X Y (H.obj 1) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) +
          ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) := by
  unfold walkingAdjunctionOrdinalWidth
  rw [Fin.sum_univ_one]
  rfl

/-- 概要：実全鎖の尾部の有限順序の幅は元の幅以下。
方針：先頭への実射の挿入の幅の式と、一辺の終点の個数の上限を使う。
規約：先頭の実面の幅。使われ方：Riehl–Verity §4.2の境界の実面の比較。 -/
lemma walkingAdjunctionOrdinalWidth_tail_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    walkingAdjunctionOrdinalWidth H.δ₀ ≤ walkingAdjunctionOrdinalWidth H := by
  have hw := walkingAdjunctionOrdinalWidth_precomp H.δ₀ (H.map' 0 1)
  rw [composableArrowPrecomp_decompose] at hw
  have hv := ordinalMapVariation_target_le (walkingAdjunctionOrderHom (H.map' 0 1))
  change walkingAdjunctionOrdinalCard X Y H.δ₀.left ≤
    walkingAdjunctionOrdinalCard X Y (H.obj 0) + _ at hv
  change walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y H.δ₀.left =
    walkingAdjunctionOrdinalWidth H.δ₀ + walkingAdjunctionOrdinalCard X Y (H.obj 0) + _ at hw
  omega

/-- 概要：最初の二辺を合成する実面の有限順序の幅は元の幅以下。
方針：元の二回の実挿入と合成辺の実挿入を比較し、変化量の合成の上限を使う。
規約：全実関手の実面を比較。使われ方：Riehl–Verity §4.2の内側の実面の基底。 -/
lemma walkingAdjunctionOrdinalWidth_first_inner_face_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H (1 : Fin (n + 3))) ≤
      walkingAdjunctionOrdinalWidth H := by
  let T := H.δ₀.δ₀
  let q := H.map' 0 1
  let g := H.δ₀.map' 0 1
  have hd : (T.precomp g).precomp q = H := by
    have h := composableArrowPrecomp_transport (composableArrowPrecomp_decompose H.δ₀) q rfl
    simpa only [eqToHom_refl, Category.comp_id] using h.trans (composableArrowPrecomp_decompose H)
  have he := congrArg (fun R : ComposableArrows (walkingAdjunctionHom X Y) (n + 2) =>
    finiteChainFace R (1 : Fin (n + 3))) hd
  rw [finiteChainFace_precomp_pair] at he
  have hp := congrArg walkingAdjunctionOrdinalWidth hd
  have hc := congrArg walkingAdjunctionOrdinalWidth he
  have hq := walkingAdjunctionOrdinalWidth_precomp (T.precomp g) q
  have hg := walkingAdjunctionOrdinalWidth_precomp T g
  have hcomp := walkingAdjunctionOrdinalWidth_precomp T (q ≫ g)
  have hv := ordinalMapVariation_comp_le (walkingAdjunctionOrderHom q) (walkingAdjunctionOrderHom g)
  rw [← walkingAdjunctionOrderHom_comp] at hv
  change walkingAdjunctionOrdinalWidth ((T.precomp g).precomp q) +
    walkingAdjunctionOrdinalCard X Y (H.obj 1) = walkingAdjunctionOrdinalWidth (T.precomp g) +
      walkingAdjunctionOrdinalCard X Y (H.obj 0) + ordinalMapVariation (walkingAdjunctionOrderHom q)
        at hq
  change walkingAdjunctionOrdinalWidth (T.precomp g) + walkingAdjunctionOrdinalCard X Y (H.obj 2) =
    walkingAdjunctionOrdinalWidth T + walkingAdjunctionOrdinalCard X Y (H.obj 1) +
      ordinalMapVariation (walkingAdjunctionOrderHom g) at hg
  change walkingAdjunctionOrdinalWidth (T.precomp (q ≫ g)) +
    walkingAdjunctionOrdinalCard X Y (H.obj 2) = walkingAdjunctionOrdinalWidth T +
      walkingAdjunctionOrdinalCard X Y (H.obj 0) +
        ordinalMapVariation (walkingAdjunctionOrderHom (q ≫ g)) at hcomp
  omega

/-- 概要：任意の実面の有限順序の幅は元の全実鎖の幅以下。
方針：先頭の面・一辺の最後の面・最初の内側の面を基底として、尾部で再帰する。
規約：全次数の全境界面を含む。使われ方：Riehl–Verity Proposition 4.2.15の実面の幅。 -/
lemma walkingAdjunctionOrdinalWidth_face_le {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (p : Fin (n + 2)),
      walkingAdjunctionOrdinalWidth (finiteChainFace H p) ≤ walkingAdjunctionOrdinalWidth H := by
  intro n
  induction n with
  | zero =>
    intro H p
    refine Fin.cases ?_ (fun k => ?_) p
    · exact walkingAdjunctionOrdinalWidth_tail_le H
    · have hk : k = 0 := by apply Fin.ext; have hlt := k.isLt; change k.val = 0; omega
      subst k
      change walkingAdjunctionOrdinalWidth (finiteChainFace H (Fin.last 1)) ≤ _
      rw [walkingAdjunctionOrdinalWidth_zero, finiteChainFace_last_obj,
        walkingAdjunctionOrdinalWidth_one]
      have hv := ordinalMapVariation_source_le (walkingAdjunctionOrderHom (H.map' 0 1))
      have ha := walkingAdjunctionCard_pair_corrections_le X Y (H.obj 0) (H.obj 0)
      have hb := walkingAdjunctionCard_pair_corrections_le X Y (H.obj 0) (H.obj 1)
      change walkingAdjunctionOrdinalCard X Y (H.obj 0) ≤
        walkingAdjunctionOrdinalCard X Y (H.obj 1) + _ at hv
      change (walkingAdjunctionOrdinalCard X Y (H.obj 0) +
        walkingAdjunctionOrdinalCard X Y (H.obj 0) -
          (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)) ≤ _
      omega
  | succ n ih =>
    intro H p
    refine Fin.cases ?_ (fun k => ?_) p
    · exact walkingAdjunctionOrdinalWidth_tail_le H
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact walkingAdjunctionOrdinalWidth_first_inner_face_le H
      · let T := finiteChainFace H.δ₀ j.succ
        have he : T.left = H.δ₀.left := finiteChainFace_first H.δ₀ j
        let f := H.map' 0 1 ≫ eqToHom he.symm
        have ht : walkingAdjunctionOrdinalWidth T ≤ walkingAdjunctionOrdinalWidth H.δ₀ :=
          ih H.δ₀ j.succ
        have hd := congrArg (fun R : ComposableArrows (walkingAdjunctionHom X Y) (n + 2) =>
          finiteChainFace R j.succ.succ) (composableArrowPrecomp_decompose H)
        rw [finiteChainFace_precomp_succ] at hd
        have heq := congrArg walkingAdjunctionOrdinalWidth hd
        change walkingAdjunctionOrdinalWidth (T.precomp f) =
          walkingAdjunctionOrdinalWidth (finiteChainFace H j.succ.succ) at heq
        have hf := walkingAdjunctionMapVariation_heq rfl he f (H.map' 0 1)
          (comp_eqToHom_heq (H.map' 0 1) he.symm)
        have hhead := walkingAdjunctionOrdinalWidth_precomp T f
        have ho := walkingAdjunctionOrdinalWidth_precomp H.δ₀ (H.map' 0 1)
        rw [composableArrowPrecomp_decompose] at ho
        have hcard := congrArg (walkingAdjunctionOrdinalCard X Y) he
        change walkingAdjunctionOrdinalWidth (T.precomp f) +
            walkingAdjunctionOrdinalCard X Y T.left =
          walkingAdjunctionOrdinalWidth T + walkingAdjunctionOrdinalCard X Y (H.obj 0) +
            ordinalMapVariation (walkingAdjunctionOrderHom f) at hhead
        change walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y H.δ₀.left =
          walkingAdjunctionOrdinalWidth H.δ₀ + walkingAdjunctionOrdinalCard X Y (H.obj 0) +
            ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) at ho
        omega

end SerrePositivity.InfinityCategories.HA.Monads
