module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpointBounds
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutBoundaryEquality

/-!
概要：元の実全単体の原子性を始頂点と終頂点の二つの有限個数で判定する。
方針：端点の個数から全ての許される切れ目を左右の外端へ回収する。
規約：対象だけの条件から全実分解の条件へ戻す過程も構成する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定した二つの端点の個数を持つ実全単体は原子的。
方針：plusの切れ目は終頂点、minusの共有点は始頂点で左右の外端と照合する。
規約：全ての実分解と全射を含む元の原子性を結論にする。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionAtomic_of_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hfirst : walkingAdjunctionOrdinalCard X Y (H.obj 0) =
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
    (hlast : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H := by
  apply (walkingAdjunctionLevelIsAtomic_iff_boundary_cuts H).mpr
  refine ⟨walkingAdjunctionSize_pos_of_endpoint_cards H hfirst hlast, ?_⟩
  intro M a hl hr
  cases M
  · have hv := (a.value (Fin.last n)).isLt
    have hs := hl (Fin.last n)
    have ht := hr (Fin.last n)
    have hc := walkingAdjunctionTargetCut_rank_card H (Fin.last n)
    rw [walkingAdjunctionSourceCut_rank] at hs
    change walkingAdjunctionTargetCorrection X ≤ 2 * (a.value (Fin.last n)).val + 0 at hs
    change 2 * (a.value (Fin.last n)).val + 0 ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) (Fin.last n) at ht
    have hL (he : X = .plus) (hz : (a.value (Fin.last n)).val = 0) :
        ∀ i, walkingAdjunctionCutRank (M := .plus) a i =
          walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i := by
      subst X
      have he := a.eq_source_of_last_zero hz
      intro i
      exact congrArg (fun c : WalkingAdjunctionPlusCut H =>
        walkingAdjunctionCutRank (M := .plus) c i) he
    have hR (he : Y = .plus)
        (hv : (a.value (Fin.last n)).val = walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n))) :
        ∀ i, walkingAdjunctionCutRank (M := .plus) a i =
          walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i := by
      subst Y
      have he := a.eq_target_of_last_card hv
      intro i
      exact congrArg (fun c : WalkingAdjunctionPlusCut H =>
        walkingAdjunctionCutRank (M := .plus) c i) he
    cases X <;> cases Y <;> simp only [walkingAdjunctionTargetCorrection] at hs hc
    · by_cases hz : (a.value (Fin.last n)).val = 0
      · exact Or.inl (hL rfl hz)
      · exact Or.inr (hR rfl (by omega))
    · exact Or.inl (hL rfl (by omega))
    · exact Or.inr (hR rfl (by omega))
    · omega
  · have hv := (a.value 0).isLt
    have hL (he : X = .minus) (hz : (a.value 0).val = 0) :
        ∀ i, walkingAdjunctionCutRank (M := .minus) a i =
          walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i := by
      subst X
      have he := a.eq_source_of_first_zero hz
      intro i
      exact congrArg (fun c : WalkingAdjunctionMinusCut H =>
        walkingAdjunctionCutRank (M := .minus) c i) he
    have hR (he : Y = .minus)
        (hv : (a.value 0).val + 1 = walkingAdjunctionOrdinalCard X Y (H.obj 0)) :
        ∀ i, walkingAdjunctionCutRank (M := .minus) a i =
          walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i := by
      subst Y
      have he := a.eq_target_of_first_top hv
      intro i
      exact congrArg (fun c : WalkingAdjunctionMinusCut H =>
        walkingAdjunctionCutRank (M := .minus) c i) he
    cases X <;> cases Y <;> simp only [walkingAdjunctionTargetCorrection] at hfirst
    · omega
    · exact Or.inr (hR rfl (by omega))
    · exact Or.inl (hL rfl (by omega))
    · by_cases hz : (a.value 0).val = 0
      · exact Or.inl (hL rfl hz)
      · exact Or.inr (hR rfl (by omega))

/-- 概要：実全単体の原子性は始頂点の補正の和と終頂点の一点という条件に同値。
方針：構成済みの必要条件と全切れ目からの十分条件を合わせる。
規約：四Homの同じ実関手を使う。使われ方：Riehl–Verity §4.1の原子の有限表示。 -/
lemma walkingAdjunctionLevelIsAtomic_iff_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      walkingAdjunctionOrdinalCard X Y (H.obj 0) =
          walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ∧
        walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1 := by
  constructor
  · exact walkingAdjunctionAtomic_endpoint_cards H
  · rintro ⟨hfirst, hlast⟩
    exact walkingAdjunctionAtomic_of_endpoint_cards H hfirst hlast

end SerrePositivity.InfinityCategories.HA.Monads
