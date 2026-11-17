module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstRefinement

/-!
概要：最初の実併合による実細分は有限順序の幅を保つ。
方針：先頭への実挿入の幅の式を再帰し、実併合の全射性で変化量の加法性を使う。
規約：幅の保存を実親の新しい入力欄にしない。
使われ方：Riehl–Verity Proposition 4.2.15の実親の幅の照合、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの法則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：先頭の一辺を変化量の和が等しい実二辺に置き換えると有限順序の幅を保つ。
方針：二回の先頭への実挿入と元の先頭の実分解の幅の式を合わせる。
規約：元の実全関手の幅を比較する。使われ方：Riehl–Verity §4.2の実親の幅の基底。 -/
lemma walkingAdjunctionOrdinalWidth_refinement_zero {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (B : walkingAdjunctionHom X Y)
    (q : H.obj (0 : Fin (n + 1)).castSucc ⟶ B)
    (g : B ⟶ H.obj (0 : Fin (n + 1)).succ)
    (hv : ordinalMapVariation (walkingAdjunctionOrderHom q) +
      ordinalMapVariation (walkingAdjunctionOrderHom g) =
        ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1))) :
    walkingAdjunctionOrdinalWidth (composableArrowRefinement H 0 B q g) =
      walkingAdjunctionOrdinalWidth H := by
  have hq := walkingAdjunctionOrdinalWidth_precomp (H.δ₀.precomp g) q
  have hg := walkingAdjunctionOrdinalWidth_precomp H.δ₀ g
  have hh := walkingAdjunctionOrdinalWidth_precomp H.δ₀ (H.map' 0 1)
  rw [composableArrowPrecomp_decompose] at hh
  rw [composableArrowRefinement_zero]
  change walkingAdjunctionOrdinalWidth ((H.δ₀.precomp g).precomp q) +
      walkingAdjunctionOrdinalCard X Y B = walkingAdjunctionOrdinalWidth (H.δ₀.precomp g) +
        walkingAdjunctionOrdinalCard X Y (H.obj 0) +
          ordinalMapVariation (walkingAdjunctionOrderHom q) at hq
  change walkingAdjunctionOrdinalWidth (H.δ₀.precomp g) +
      walkingAdjunctionOrdinalCard X Y (H.obj 1) = walkingAdjunctionOrdinalWidth H.δ₀ +
        walkingAdjunctionOrdinalCard X Y B + ordinalMapVariation (walkingAdjunctionOrderHom g) at hg
  change walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y (H.obj 1) =
    walkingAdjunctionOrdinalWidth H.δ₀ + walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) at hh
  omega

/-- 概要：変化量の和が元の実辺と等しい実二辺への細分は有限順序の幅を保つ。
方針：指定位置で再帰し、先頭の実射の対象の輸送で変化量が変わらないことを使う。
規約：全実位置。使われ方：Riehl–Verity §4.2の実親の幅の保存。 -/
lemma walkingAdjunctionOrdinalWidth_refinement {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (k : Fin (n + 1))
      (B : walkingAdjunctionHom X Y) (q : H.obj k.castSucc ⟶ B) (g : B ⟶ H.obj k.succ),
      ordinalMapVariation (walkingAdjunctionOrderHom q) +
        ordinalMapVariation (walkingAdjunctionOrderHom g) =
          ordinalMapVariation (walkingAdjunctionOrderHom
            (H.map (homOfLE (Fin.castSucc_le_succ k)))) →
      walkingAdjunctionOrdinalWidth (composableArrowRefinement H k B q g) =
        walkingAdjunctionOrdinalWidth H := by
  intro n
  induction n with
  | zero =>
    intro H k B q g hv
    have hk : k = 0 := by apply Fin.ext; have hlt := k.isLt; change k.val = 0; omega
    subst k
    exact walkingAdjunctionOrdinalWidth_refinement_zero H B q g hv
  | succ n ih =>
    intro H k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g hv
      exact walkingAdjunctionOrdinalWidth_refinement_zero H B q g hv
    · intro B q g hv
      let R := composableArrowRefinement H.δ₀ k B q g
      have hr : walkingAdjunctionOrdinalWidth R = walkingAdjunctionOrdinalWidth H.δ₀ :=
        ih H.δ₀ k B q g hv
      have he : R.left = H.δ₀.left := composableArrowRefinement_first H.δ₀ k B q g
      let f := H.map' 0 1 ≫ eqToHom he.symm
      have hf := walkingAdjunctionMapVariation_heq rfl he f (H.map' 0 1)
        (comp_eqToHom_heq (H.map' 0 1) he.symm)
      have hh := walkingAdjunctionOrdinalWidth_precomp R f
      have ho := walkingAdjunctionOrdinalWidth_precomp H.δ₀ (H.map' 0 1)
      rw [composableArrowPrecomp_decompose] at ho
      have hc := congrArg (walkingAdjunctionOrdinalCard X Y) he
      erw [composableArrowRefinement_succ]
      change walkingAdjunctionOrdinalWidth (R.precomp f) = walkingAdjunctionOrdinalWidth H
      omega

/-- 概要：実底併合による実細分は有限順序の幅を保つ。
方針：実併合の全射性と元の射への因子化から、変化量の和を元の辺へ戻す。
規約：幅の保存を仮定せず構成した親へ適用する。使われ方：Riehl–Verity §4.2の実親。 -/
lemma walkingAdjunctionBottomMergeRefinement_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionBottomMergeRefinement H k m hA h1) =
      walkingAdjunctionOrdinalWidth H := by
  let q := walkingAdjunctionBottomMergeArrow (H.obj k.castSucc) m hA
  let g := walkingAdjunctionBottomMergeResidual (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  apply walkingAdjunctionOrdinalWidth_refinement
  have hv := ordinalMapVariation_comp_of_surjective (walkingAdjunctionOrderHom q)
    (walkingAdjunctionOrderHom g) (walkingAdjunctionBottomMergeArrow_surjective _ _ _)
  have hf : (walkingAdjunctionOrderHom g).comp (walkingAdjunctionOrderHom q) =
      walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) := by
    rw [← walkingAdjunctionOrderHom_comp]
    exact congrArg (fun f => walkingAdjunctionOrderHom f)
      (walkingAdjunctionBottomMerge_factor (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)
  exact hv.symm.trans (congrArg ordinalMapVariation hf)

/-- 概要：元の実最小元から選んだ最初の実親は有限順序の幅を保つ。
方針：構成済みの実併合の幅の法則を、実最小元で定まる全関手へ適用する。
規約：元の全実関手の幅の等式。使われ方：Riehl–Verity §4.2の実親の対応。 -/
lemma walkingAdjunctionFirstRefinement_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement H ha hnd) =
      walkingAdjunctionOrdinalWidth H :=
  walkingAdjunctionBottomMergeRefinement_ordinalWidth _ _ _ _ _

end SerrePositivity.InfinityCategories.HA.Monads
