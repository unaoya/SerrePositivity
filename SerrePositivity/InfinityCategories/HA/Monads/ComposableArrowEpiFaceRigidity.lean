module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowFaceRigidity

/-!
概要：挿入左辺がepiなら、指定面・挿入対象・左辺だけで実親を回収する。
方針：面に現れる二辺の合成を比較して右辺を消去で定める。
規約：係数移送の前後で全実射を保持する。
使われ方：Riehl–Verity §4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：同じepiな左因子と同じ合成は、係数移送後の右因子を一意に定める。
方針：両端と中間対象を同一視してepiの消去を適用する。
規約：対象の等式も明示する。使われ方：Riehl–Verity §4.1の右辺の回収。 -/
lemma rightFactor_heq_of_epi_comp_heq {A B D A' B' D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (q : A ⟶ B) (q' : A' ⟶ B') (g : B ⟶ D) (g' : B' ⟶ D')
    [Epi q] (hq : HEq q q') (hc : HEq (q ≫ g) (q' ≫ g')) : HEq g g' := by
  subst A'
  subst B'
  subst D'
  have he : q = q' := eq_of_heq hq
  subst q'
  exact heq_of_eq ((cancel_epi q).mp (eq_of_heq hc))

/-- 概要：epiな挿入左辺・中間対象・指定面が一致する二つの実全鎖は一致する。
方針：指定面内の合成を回収し、右辺をepiの消去で一致させる。
規約：全実関手の等式。使われ方：Riehl–Verity §4.1の実親の一意性。 -/
lemma composableArrow_eq_of_face_and_epi_left {n : ℕ}
    {F G : ComposableArrows C (n + 2)} (k : Fin (n + 1))
    (hface : finiteChainFace F k.succ.castSucc = finiteChainFace G k.succ.castSucc)
    (hmid : F.obj k.succ.castSucc = G.obj k.succ.castSucc)
    (hleft : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))))
    [Epi (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))] : F = G := by
  have ha : k.castSucc.castSucc ≠ k.succ.castSucc := by
    intro he
    have hv := congrArg (fun t : Fin (n + 3) => t.val) he
    change k.val = k.val + 1 at hv
    omega
  have hc : k.succ.succ ≠ k.succ.castSucc := by
    intro he
    have hv := congrArg (fun t : Fin (n + 3) => t.val) he
    change k.val + 2 = k.val + 1 at hv
    omega
  have had : k.castSucc.castSucc ≤ k.succ.succ := by
    change k.val ≤ k.val + 2
    omega
  apply composableArrow_eq_of_face_and_incident_edges k hface hmid hleft
  apply rightFactor_heq_of_epi_comp_heq
    (finiteChainFace_obj_eq _ hface _ ha) hmid (finiteChainFace_obj_eq _ hface _ hc)
    (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
    (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) _ _ hleft
  have hf : F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      F.map (homOfLE (Fin.castSucc_le_succ k.succ)) = F.map (homOfLE had) := by
    rw [← F.map_comp]
    rfl
  have hg : G.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      G.map (homOfLE (Fin.castSucc_le_succ k.succ)) = G.map (homOfLE had) := by
    rw [← G.map_comp]
    rfl
  rw [hf, hg]
  exact finiteChainFace_map_heq _ hface had ha hc

end SerrePositivity.InfinityCategories.HA.Monads
