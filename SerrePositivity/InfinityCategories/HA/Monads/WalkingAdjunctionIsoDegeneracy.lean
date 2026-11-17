module

public import SerrePositivity.InfinityCategories.HA.Monads.NerveCollapsedEdges
public import SerrePositivity.InfinityCategories.HA.Monads.NerveDegeneracyEdges
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIsomorphismProfiles
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegeneracies

/-!
概要：元の四Homの同型は恒等射の輸送であり、非退化な全単体の全隣接辺は非同型。
方針：実同型の個数・値の保存と元のnerveの実縮約を合わせる。
規約：非退化性は元のHomの単体集合で判定する。
使われ方：Riehl–Verity §3.1・§4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の同型な実辺の検出。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：四Homの元の実同型は対象の等式による恒等射。
方針：個数から対象を同一視し、全点の値の保存と忠実性で実射を回収する。
規約：同型の剛性を仮定しない。使われ方：Riehl–Verity §3.1の実退化の検出。 -/
lemma walkingAdjunctionIsIso_eqToHom {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    ∃ h : A = B, f = eqToHom h := by
  have hAB : A = B := by
    apply walkingAdjunctionWeight_injective X Y
    have hc := walkingAdjunctionCard_eq_of_isIso f
    have ha := walkingAdjunctionOrdinalCard_weight X Y A
    have hb := walkingAdjunctionOrdinalCard_weight X Y B
    omega
  refine ⟨hAB, ?_⟩
  apply walkingAdjunctionOrderHom_injective
  apply OrderHom.ext
  funext i
  apply Fin.ext
  exact (walkingAdjunctionOrderHom_val_of_isIso f i).trans
    (walkingAdjunctionOrderHom_val_of_isIso (eqToHom hAB) i).symm

/-- 概要：同型な隣接実辺を持つ全単体は元のHomの単体集合で退化。
方針：実同型を恒等射の輸送へ戻して元の実面・退化の縮約を適用する。
規約：正の全次元を含む。使われ方：Riehl–Verity §4.1の非退化な親の実辺の検収。 -/
lemma walkingAdjunctionHomShape_degenerate_of_isIso {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (j : Fin (n + 1))
    [IsIso (H.map (homOfLE (Fin.castSucc_le_succ j)))] :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).degenerate (n + 1) := by
  obtain ⟨ho, hm⟩ := walkingAdjunctionIsIso_eqToHom (H.map (homOfLE (Fin.castSucc_le_succ j)))
  exact uliftNerve_degenerate_of_eqToHom_edge H j ho hm

/-- 概要：元の全単体の非退化性は全隣接実辺が非同型であることと同値。
方針：同型なら実縮約し、退化なら実退化で重なる辺の同型を取り出す。
規約：元のHomのnerveの非退化性の両方向。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionHomShape_nondegenerate_iff_no_isIso {n : ℕ}
    {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1) ↔
      ∀ j : Fin (n + 1), ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ j))) := by
  constructor
  · intro hnd j hj
    have := hj
    exact (SSet.mem_nonDegenerate_iff_notMem_degenerate _ _).mp hnd
      (walkingAdjunctionHomShape_degenerate_of_isIso H j)
  · intro hno
    apply (SSet.mem_nonDegenerate_iff_notMem_degenerate _ _).mpr
    intro hd
    rw [SSet.degenerate_eq_iUnion_range_σ] at hd
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hd
    obtain ⟨t, ht⟩ := hj
    have he : (nerve (walkingAdjunctionHom X Y)).σ j t.down = H := congrArg ULift.down ht
    apply hno j
    rw [← he]
    exact nerve_degeneracy_edge_isIso t.down j

end SerrePositivity.InfinityCategories.HA.Monads
