module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces

/-!
概要：同じ指定面を持つ実鎖の全対象と、挿入頂点に接する二辺から元の全関手を回収する。
方針：面の有限順序埋め込みの補集合は一点だけであることを使う。
規約：辺は異種等式、全体は元の圏への実関手の等式で比較する。
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

/-- 概要：同じ実面の全対象は、除いた頂点以外で一致する。
方針：一点を飛ばす埋め込みの像に頂点を戻す。規約：実対象の等式。
使われ方：Riehl–Verity §4.1の指定面からの親の回収。 -/
lemma finiteChainFace_obj_eq {n : ℕ} {F G : ComposableArrows C (n + 1)}
    (p : Fin (n + 2)) (h : finiteChainFace F p = finiteChainFace G p)
    (i : Fin (n + 2)) (hi : i ≠ p) : F.obj i = G.obj i := by
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
  exact CategoryTheory.Functor.congr_obj h j

/-- 概要：同じ実面の全射は、除いた頂点を両端に含まないとき一致する。
方針：実射の両端を埋め込みの像へ戻して面の全関手の等式を使う。
規約：対象の等式の前は異種等式。使われ方：Riehl–Verity §4.1の親の実辺の回収。 -/
lemma finiteChainFace_map_heq {n : ℕ} {F G : ComposableArrows C (n + 1)}
    (p : Fin (n + 2)) (h : finiteChainFace F p = finiteChainFace G p)
    {a b : Fin (n + 2)} (hab : a ≤ b) (ha : a ≠ p) (hb : b ≠ p) :
    HEq (F.map (homOfLE hab)) (G.map (homOfLE hab)) := by
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq ha
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hb
  have hij : i ≤ j := (Fin.strictMono_succAbove p).le_iff_le.mp hab
  exact CategoryTheory.Functor.hcongr_hom h (homOfLE hij)

/-- 概要：指定面・挿入頂点・接する実二辺は元の実全鎖を一意に定める。
方針：他の対象と隣接辺を面から回収して実鎖の外延性を適用する。
規約：全関手の等式を結論とする。使われ方：Riehl–Verity §4.1の実親の一意性。 -/
lemma composableArrow_eq_of_face_and_incident_edges {n : ℕ}
    {F G : ComposableArrows C (n + 2)} (k : Fin (n + 1))
    (hface : finiteChainFace F k.succ.castSucc = finiteChainFace G k.succ.castSucc)
    (hmid : F.obj k.succ.castSucc = G.obj k.succ.castSucc)
    (hleft : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))))
    (hright : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.succ)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.succ)))) : F = G := by
  classical
  have ho (i : Fin (n + 3)) : F.obj i = G.obj i := by
    by_cases hi : i = k.succ.castSucc
    · subst i
      exact hmid
    · exact finiteChainFace_obj_eq _ hface i hi
  apply ComposableArrows.ext ho
  intro i hi
  let j : Fin (n + 2) := ⟨i, hi⟩
  apply (conj_eqToHom_iff_heq _ _ (ho j.castSucc) (ho j.succ)).mpr
  change HEq (F.map (homOfLE (Fin.castSucc_le_succ j)))
    (G.map (homOfLE (Fin.castSucc_le_succ j)))
  by_cases hl : j = k.castSucc
  · rw [hl]
    exact hleft
  by_cases hr : j = k.succ
  · rw [hr]
    exact hright
  apply finiteChainFace_map_heq _ hface (Fin.castSucc_le_succ j)
  · intro he
    apply hr
    apply Fin.ext
    change j.val = k.val + 1
    exact congrArg (fun t : Fin (n + 3) => t.val) he
  · intro he
    apply hl
    apply Fin.ext
    have hv := congrArg (fun t : Fin (n + 3) => t.val) he
    change j.val + 1 = k.val + 1 at hv
    change j.val = k.val
    omega

end SerrePositivity.InfinityCategories.HA.Monads
