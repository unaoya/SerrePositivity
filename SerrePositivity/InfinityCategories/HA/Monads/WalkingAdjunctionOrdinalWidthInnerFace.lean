module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthFaces
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowInnerFace

/-!
概要：内側の実面の幅の変化を、合成する二辺の変化量の差として計算する。
方針：先頭の二辺の実挿入から始め、尾部へ再帰して両端の補正を相殺する。
規約：元の全実鎖の等式であり、幅の差の新しい証人を入力に置かない。
使われ方：Riehl–Verity Proposition 4.2.15の厳密な幅の減少、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの面の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最初の内側の実面の幅の減少は、最初の二辺の変化量の合成での減少に等しい。
方針：二度の実挿入と一度の合成辺の実挿入を比較する。
規約：自然数の等式。使われ方：Riehl–Verity §4.2の実面の幅の欠損の基底。 -/
lemma walkingAdjunctionOrdinalWidth_first_inner_defect {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H (1 : Fin (n + 3))) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.δ₀.map' 0 1)) =
    walkingAdjunctionOrdinalWidth H + ordinalMapVariation
      (walkingAdjunctionOrderHom (H.map' 0 1 ≫ H.δ₀.map' 0 1)) := by
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
  change walkingAdjunctionOrdinalWidth (finiteChainFace H (1 : Fin (n + 3))) +
    ordinalMapVariation (walkingAdjunctionOrderHom q) +
    ordinalMapVariation (walkingAdjunctionOrderHom g) =
    walkingAdjunctionOrdinalWidth H + ordinalMapVariation (walkingAdjunctionOrderHom (q ≫ g))
  omega

/-- 概要：任意の内側の実面の幅の欠損は、指定二辺の変化量の合成での欠損。
方針：最初の面から尾部で帰納し、先頭の実対象と実射の輸送の補正を相殺する。
規約：全実位置・全次数。使われ方：Riehl–Verity §4.2の厳密な幅の比較。 -/
lemma walkingAdjunctionOrdinalWidth_inner_defect {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1)),
      walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) +
        ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))) +
        ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ k.succ)))) =
      walkingAdjunctionOrdinalWidth H + ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
          H.map (homOfLE (Fin.castSucc_le_succ k.succ)))) := by
  intro n
  induction n with
  | zero =>
    intro H k
    have hk : k = 0 := by
      apply Fin.ext
      have h := k.isLt
      change k.val = 0
      omega
    subst k
    exact walkingAdjunctionOrdinalWidth_first_inner_defect H
  | succ n ih =>
    intro H k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact walkingAdjunctionOrdinalWidth_first_inner_defect H
    · let T := finiteChainFace H.δ₀ j.succ.castSucc
      have he : T.left = H.δ₀.left := finiteChainFace_first H.δ₀ j.castSucc
      let f := H.map' 0 1 ≫ eqToHom he.symm
      have ht := ih H.δ₀ j
      have hd := congrArg (fun R : ComposableArrows (walkingAdjunctionHom X Y) (n + 3) =>
        finiteChainFace R j.succ.succ.castSucc) (composableArrowPrecomp_decompose H)
      change finiteChainFace (H.δ₀.precomp (H.map' 0 1)) j.castSucc.succ.succ =
        finiteChainFace H j.castSucc.succ.succ at hd
      rw [finiteChainFace_precomp_succ] at hd
      have heq := congrArg walkingAdjunctionOrdinalWidth hd
      change walkingAdjunctionOrdinalWidth (T.precomp f) =
        walkingAdjunctionOrdinalWidth (finiteChainFace H j.succ.succ.castSucc) at heq
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
      change walkingAdjunctionOrdinalWidth T +
        ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ j.succ.castSucc)))) +
        ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ j.succ.succ)))) =
        walkingAdjunctionOrdinalWidth H.δ₀ + ordinalMapVariation (walkingAdjunctionOrderHom
          (H.map (homOfLE (Fin.castSucc_le_succ j.succ.castSucc)) ≫
            H.map (homOfLE (Fin.castSucc_le_succ j.succ.succ)))) at ht
      omega

/-- 概要：指定二辺の変化量が合成で真に減れば、その内側の実面の幅も真に減る。
方針：実幅の欠損の等式へ変化量の厳密な不等式を入れる。
規約：元の全実面の幅。使われ方：Riehl–Verity §4.2のfiltrationの幅による減少。 -/
lemma walkingAdjunctionOrdinalWidth_inner_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1))
    (hv : ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
          H.map (homOfLE (Fin.castSucc_le_succ k.succ)))) <
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))) +
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.succ))))) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) <
      walkingAdjunctionOrdinalWidth H := by
  have h := walkingAdjunctionOrdinalWidth_inner_defect n H k
  omega

end SerrePositivity.InfinityCategories.HA.Monads
