module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowLastFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRemoveBottomPrefix

/-!
概要：最後の実面と一点の終点を持つ実全鎖は全関手として一意。
方針：面から最後以前の全対象・辺を回収し、最後の射は一点への一意性を使う。
規約：最後の実辺の一致を入力に置かない。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の元の実親の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：同じ最後の実面と一点の実終点を持つ二つの全鎖は一致する。
方針：最後の実対象は個数で同一視し、最後の実辺は一点への射の一意性で回収する。
規約：全実関手の等式。使われ方：Riehl–Verity Lemma 4.1.4の実親の一意性。 -/
lemma walkingAdjunction_eq_of_last_face_and_card_one {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F G : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (hface : finiteChainFace F (Fin.last (n + 1)) = finiteChainFace G (Fin.last (n + 1)))
    (hf : walkingAdjunctionOrdinalCard X Y (F.obj (Fin.last (n + 1))) = 1)
    (hg : walkingAdjunctionOrdinalCard X Y (G.obj (Fin.last (n + 1))) = 1) : F = G := by
  have hl : F.obj (Fin.last (n + 1)) = G.obj (Fin.last (n + 1)) :=
    walkingAdjunctionOrdinalCard_injective X Y (hf.trans hg.symm)
  have ho (i : Fin (n + 2)) : F.obj i = G.obj i := by
    refine Fin.lastCases hl (fun j => ?_) i
    have he := CategoryTheory.Functor.congr_obj hface j
    rw [finiteChainFace_last_obj, finiteChainFace_last_obj] at he
    exact he
  have hm (j : Fin (n + 1)) :
      HEq (F.map (homOfLE (Fin.castSucc_le_succ j)))
        (G.map (homOfLE (Fin.castSucc_le_succ j))) := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · apply (conj_eqToHom_iff_heq _ _ (ho (Fin.last n).castSucc) (ho (Fin.last n).succ)).mp
      exact walkingAdjunctionHom_ext_of_card_one_target _ _ hf
    · cases n with
      | zero => exact Fin.elim0 j
      | succ n =>
        exact (finiteChainFace_last_edge F j).symm.trans
          ((CategoryTheory.Functor.hcongr_hom hface
            (homOfLE (Fin.castSucc_le_succ j))).trans (finiteChainFace_last_edge G j))
  refine ComposableArrows.ext ho ?_
  intro i hi
  let j : Fin (n + 1) := ⟨i, hi⟩
  exact (conj_eqToHom_iff_heq _ _ (ho j.castSucc) (ho j.succ)).mpr (hm j)

end SerrePositivity.InfinityCategories.HA.Monads
