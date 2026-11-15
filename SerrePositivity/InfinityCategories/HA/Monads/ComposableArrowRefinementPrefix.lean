module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementPositions

/-!
概要：実細分の指定位置より前の実対象・辺と、挿入した左の実射を回収する。
方針：対象は指定面、辺は実precompの再帰と対象の輸送で比較する。
規約：全鎖の元の実射を異種等式で保持する。
使われ方：Riehl–Verity §4.1–§4.2の最初の折り返しの保存、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：挿入位置より前の対象は元の実鎖の対象。
方針：指定面の全関手の等式を同じ有限点で評価する。
規約：合成の検収を使い対象の等式を得る。使われ方：Riehl–Verity §4.1の位置の保存。 -/
lemma composableArrowRefinement_before_obj {n : ℕ} (F : ComposableArrows C (n + 1))
    (k : Fin (n + 1)) (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
    (fac : q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)))
    (i : Fin (n + 2)) (hi : i.val ≤ k.val) :
    (composableArrowRefinement F k B q g).obj i.castSucc = F.obj i := by
  have he := CategoryTheory.Functor.congr_obj (composableArrowRefinement_face n F k B q g fac) i
  change (composableArrowRefinement F k B q g).obj (k.succ.castSucc.succAbove i) = F.obj i at he
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < k.val + 1; omega)] at he
  exact he

/-- 概要：細分で挿入した頂点の左の実射は指定した左因子。
方針：実precompの先頭の射と尾部を再帰して比較する。
規約：元の実射を異種等式で保持する。使われ方：Riehl–Verity §4.1の最初の併合の保存。 -/
lemma composableArrowRefinement_left_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.castSucc))) q := by
  intro n
  induction n with
  | zero =>
    intro F k B q g
    have hk : k = 0 := by apply Fin.ext; have hi := k.isLt; change k.val = 0; omega
    subst k
    rw [composableArrowRefinement_zero]
    rfl
  | succ n ih =>
    intro F k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g
      rw [composableArrowRefinement_zero]
      rfl
    · intro B q g
      erw [composableArrowRefinement_succ]
      change HEq ((composableArrowRefinement F.δ₀ k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.castSucc))) q
      exact ih F.δ₀ k B q g

/-- 概要：細分の位置より前の実辺は元の実辺。
方針：尾部で再帰し、先頭は対象の等式による右の輸送を除く。
規約：各実射を異種等式として回収する。使われ方：Riehl–Verity §4.1の最初の位置の保存。 -/
lemma composableArrowRefinement_before_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
      (j : Fin (n + 1)), j < k →
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ j.castSucc)))
          (F.map (homOfLE (Fin.castSucc_le_succ j))) := by
  intro n
  induction n with
  | zero =>
    intro F k B q g j hj
    have hk := k.isLt
    have hj' := j.isLt
    change j.val < k.val at hj
    omega
  | succ n ih =>
    intro F k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g j hj
      change j.val < 0 at hj
      omega
    · intro B q g j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hj
        erw [composableArrowRefinement_succ]
        change HEq
          (F.map' 0 1 ≫ eqToHom (composableArrowRefinement_first F.δ₀ k B q g).symm)
          (F.map' 0 1)
        exact comp_eqToHom_heq _ _
      · intro hj
        erw [composableArrowRefinement_succ]
        change HEq ((composableArrowRefinement F.δ₀ k B q g).map
          (homOfLE (Fin.castSucc_le_succ j.castSucc)))
            (F.δ₀.map (homOfLE (Fin.castSucc_le_succ j)))
        exact ih F.δ₀ k B q g j (by
          change j.val + 1 < k.val + 1 at hj
          exact Nat.lt_of_succ_lt_succ hj)

end SerrePositivity.InfinityCategories.HA.Monads
