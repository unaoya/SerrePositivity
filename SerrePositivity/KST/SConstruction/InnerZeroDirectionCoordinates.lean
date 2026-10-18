module
public import SerrePositivity.KST.SConstruction.InnerVariableCoordinates
public import SerrePositivity.KST.SConstruction.ZeroDirections

/-! # 最内側の零次数と最後の零方向
概要：可変の最内側の添字に零次数を代入し、既存の零方向の添字と照合する。
方針：最後の座標と、それ以外の座標に分けて比較する。
規約：零方向は Fin.last r。使われ方：全零境界への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open scoped Simplicial

/-- 概要：同じ次数を最後にも代入すると全方向の対角添字になる。
方針：最後の座標と castSucc の座標の計算を使う。
規約：方向数零も含む。使われ方：既存の反復実現との同定。 -/
lemma innerVariableIndex_obj_diagonal (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    (innerVariableIndex r (fun _ => d)).obj d = fun _ => d := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact innerVariableIndex_obj_last r (fun _ => d) d
  · exact innerVariableIndex_obj_castSucc r (fun _ => d) d j

/-- 概要：最内側に零次数を代入することは最後の零方向を固定することと一致。
方針：最後の座標と補集合の座標を個別に計算する。
規約：既存の zeroDirectionsIndex を使う。使われ方：定数部分の境界への包含。 -/
lemma innerVariableIndex_obj_zero (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    (innerVariableIndex r (fun _ => d)).obj (Opposite.op ⦋0⦌) =
      (zeroDirectionsIndex {Fin.last r}).obj (fun _ => d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [innerVariableIndex_obj_last]
    simp [zeroDirectionsIndex, zeroCoordinateFunctor]
  · rw [innerVariableIndex_obj_castSucc]
    simp [zeroDirectionsIndex, zeroCoordinateFunctor, Fin.castSucc_ne_last]

private lemma eqToHom_pi_apply {r : ℕ} {d e : Fin r → SimplexCategoryᵒᵖ}
    (h : d = e) (i : Fin r) :
    (eqToHom h) i = eqToHom (congrArg (fun q => q i) h) := by
  cases h
  rfl

private lemma zeroCoordinateNat_true_transport {r : ℕ} (i : Fin r)
    (d : Fin r → SimplexCategoryᵒᵖ) (b : Bool) (hb : b = true)
    (h0 : Opposite.op ⦋0⦌ = (zeroCoordinateFunctor i b).obj d) :
    eqToHom h0 ≫ (zeroCoordinateNat i b).app d =
      (SimplexCategory.const (d i).unop ⦋0⦌ 0).op := by
  subst b
  exact Category.id_comp _

private lemma zeroCoordinateNat_false_transport {r : ℕ} (i : Fin r)
    (d : Fin r → SimplexCategoryᵒᵖ) (b : Bool) (hb : b = false)
    (h0 : d i = (zeroCoordinateFunctor i b).obj d) :
    eqToHom h0 ≫ (zeroCoordinateNat i b).app d = 𝟙 (d i) := by
  subst b
  exact Category.id_comp _

/-- 概要：零次数からの最内側の作用素は既存の最後の零方向の包含そのもの。
方針：座標の輸送を明示し、最後とそれ以外の作用素を比較する。
規約：始域と終域の添字の同定を両端に置く。使われ方：全零境界への降下。 -/
lemma innerVariableIndex_zero_map (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    eqToHom (innerVariableIndex_obj_zero r d).symm ≫
      (innerVariableIndex r (fun _ => d)).map
        (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫
      eqToHom (innerVariableIndex_obj_diagonal r d) =
        (zeroDirectionsIndexNat {Fin.last r}).app (fun _ => d) := by
  funext i
  simp only [Pi.comp_apply, eqToHom_pi_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hb : decide (Fin.last r ∈ ({Fin.last r} : Finset (Fin (r + 1)))) = true := by simp
    have h0 : Opposite.op ⦋0⦌ =
        (zeroCoordinateFunctor (Fin.last r)
          (decide (Fin.last r ∈ ({Fin.last r} : Finset (Fin (r + 1)))))).obj (fun _ => d) := by
      rw [hb]
      rfl
    apply (cancel_epi (eqToHom h0)).1
    calc
      _ = eqToHom (innerVariableIndex_obj_last r (fun _ => d) (Opposite.op ⦋0⦌)).symm ≫
          ((innerVariableIndex r (fun _ => d)).map
            (SimplexCategory.const d.unop ⦋0⦌ 0).op) (Fin.last r) ≫
          eqToHom (innerVariableIndex_obj_last r (fun _ => d) d) := by
        simp only [← Category.assoc, eqToHom_trans]
      _ = _ := innerVariableIndex_map_last r (fun _ => d)
        (SimplexCategory.const d.unop ⦋0⦌ 0).op
      _ = _ := (zeroCoordinateNat_true_transport (Fin.last r) (fun _ => d) _ hb h0).symm
  · have hb : decide (j.castSucc ∈ ({Fin.last r} : Finset (Fin (r + 1)))) = false := by simp
    have h0 : d =
        (zeroCoordinateFunctor j.castSucc
          (decide (j.castSucc ∈ ({Fin.last r} : Finset (Fin (r + 1)))))).obj (fun _ => d) := by
      rw [hb]
      rfl
    apply (cancel_epi (eqToHom h0)).1
    calc
      _ = eqToHom (innerVariableIndex_obj_castSucc r (fun _ => d) (Opposite.op ⦋0⦌) j).symm ≫
          ((innerVariableIndex r (fun _ => d)).map
            (SimplexCategory.const d.unop ⦋0⦌ 0).op) j.castSucc ≫
          eqToHom (innerVariableIndex_obj_castSucc r (fun _ => d) d j) := by
        simp only [← Category.assoc, eqToHom_trans]
      _ = _ := innerVariableIndex_map_castSucc r (fun _ => d)
        (SimplexCategory.const d.unop ⦋0⦌ 0).op j
      _ = _ := (zeroCoordinateNat_false_transport j.castSucc (fun _ => d) _ hb h0).symm

end SerrePositivity.KST.SConstruction
