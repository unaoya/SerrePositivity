module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowAppend
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces

/-!
概要：実終端射を挿入した実全鎖の最後の面は元の全鎖。
方針：実尾部と先頭への挿入の面の合成則で再帰する。
規約：全射を含む元の関手の等式を保つ。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さでの実親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実指定面の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：終端に挿入した実対象を最後の面で取り除くと元の実全鎖。
方針：実尾部への再帰と先頭の対象の等式による輸送を照合する。
規約：元の全関手の等式。使われ方：Riehl–Verity Lemma 4.1.4の指定面。 -/
lemma composableArrowAppend_face_last :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (f : F.obj (Fin.last n) ⟶ B),
      finiteChainFace (composableArrowAppend F B f) (Fin.last (n + 1)) = F := by
  intro n
  induction n with
  | zero =>
    intro F B f
    rw [composableArrowAppend_zero]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => by omega)
    have hi : i = 0 := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = 0
      omega
    subst i
    rfl
  | succ n ih =>
    intro F B f
    let R := composableArrowAppend F.δ₀ B f
    have hr : finiteChainFace R (Fin.last (n + 1)) = F.δ₀ := ih F.δ₀ B f
    have h0 : (finiteChainFace R (Fin.last (n + 1))).left = F.δ₀.left :=
      congrArg (fun H : ComposableArrows C n => H.left) hr
    rw [composableArrowAppend_succ]
    change finiteChainFace (R.precomp
      (F.map' 0 1 ≫ eqToHom (composableArrowAppend_first F.δ₀ B f).symm))
      (Fin.last n).succ.succ = F
    rw [finiteChainFace_precomp_succ]
    have hw :
        (F.map' 0 1 ≫ eqToHom (composableArrowAppend_first F.δ₀ B f).symm) ≫
          eqToHom (finiteChainFace_first R (Fin.last n)).symm =
            F.map' 0 1 ≫ eqToHom h0.symm := by
      simp only [Category.assoc, eqToHom_trans]
    rw [hw]
    exact (composableArrowPrecomp_transport hr (F.map' 0 1) h0).trans
      (composableArrowPrecomp_decompose F)

end SerrePositivity.InfinityCategories.HA.Monads
