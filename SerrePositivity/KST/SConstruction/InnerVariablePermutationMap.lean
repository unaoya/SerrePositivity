module
public import SerrePositivity.KST.SConstruction.InnerVariablePermutation

/-! # 元の可変添字の全方向作用と巡回置換
概要：内側と外側の二つの元の作用を合成すると、全添字の巡回置換の作用そのものになる。
方針：最後の座標と残りの座標で、既存の作用の式と等号の輸送を合成する。
規約：等号の輸送を両側に明示する。使われ方：全多単体的な座標比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

private lemma eqToHom_pi_apply {r : ℕ} {d e : Fin r → SimplexCategoryᵒᵖ}
    (h : d = e) (i : Fin r) :
    (eqToHom h) i = eqToHom (congrArg (fun q => q i) h) := by
  cases h
  rfl

/-- 内外の全次数変更の合成は、元の添字と巡回置換の同定の下で厳密に一致する。 -/
lemma innerVariableIndex_map_permutation (r : ℕ)
    {d e : Fin (r + 1) → SimplexCategoryᵒᵖ} (f : d ⟶ e) :
    innerVariableOuterMap r (fun i => f i.succ) (d 0) ≫
        (innerVariableIndex r (fun i => e i.succ)).map (f 0) ≫
          eqToHom (innerVariableIndex_obj_permutation r e) =
      eqToHom (innerVariableIndex_obj_permutation r d) ≫
        (Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ)
          (finRotate (r + 1))).map f := by
  funext i
  change (innerVariableOuterMap r (fun i => f i.succ) (d 0) i ≫
      ((innerVariableIndex r (fun i => e i.succ)).map (f 0)) i ≫
        (eqToHom (innerVariableIndex_obj_permutation r e)) i) =
    (eqToHom (innerVariableIndex_obj_permutation r d)) i ≫ f (finRotate (r + 1) i)
  simp only [eqToHom_pi_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply (cancel_epi (eqToHom
      (innerVariableIndex_obj_last r (fun i => d i.succ) (d 0)).symm)).mp
    have h := congrArg₂ (fun a b => a ≫ b)
      (innerVariableOuterMap_last r (fun i => f i.succ) (d 0))
      (innerVariableIndex_map_last r (fun i => e i.succ) (f 0))
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp] at h
    have hr : (0 : Fin (r + 1)) = finRotate (r + 1) (Fin.last r) := finRotate_last.symm
    have hh := congrArg (fun t => t ≫ eqToHom (congrArg e hr)) h
    have hn := eqToHom_naturality f hr
    simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id] using hh.trans hn
  · apply (cancel_epi (eqToHom
      (innerVariableIndex_obj_castSucc r (fun i => d i.succ) (d 0) j).symm)).mp
    have h := congrArg₂ (fun a b => a ≫ b)
      (innerVariableOuterMap_castSucc r (fun i => f i.succ) (d 0) j)
      (innerVariableIndex_map_castSucc r (fun i => e i.succ) (f 0) j)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id] at h
    have hr : j.succ = finRotate (r + 1) j.castSucc := (finRotate_castSucc r j).symm
    have hh := congrArg (fun t => t ≫ eqToHom (congrArg e hr)) h
    have hn := eqToHom_naturality f hr
    simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id] using hh.trans hn

end SerrePositivity.KST.SConstruction
