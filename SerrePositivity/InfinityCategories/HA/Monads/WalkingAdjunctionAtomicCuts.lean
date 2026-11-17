module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicBoundaries

/-!
概要：原子性を、両外端の間の切れ目が二つの外端だけである条件へ移す。
方針：切れ目からの実分解と、その両方向の往復を使う。
規約：左右の実関手の存在を条件として加えず、構成済みの実分解を適用する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：原子性は許される全切れ目の順位が左右の外端のいずれかである条件と同値。
方針：切れ目の実分解を原子性へ入れ、逆向きは元の実分解の切れ目で判定する。
規約：全頂点の順位と長さが正である条件を保持する。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionLevelIsAtomic_iff_boundary_cuts {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      0 < walkingAdjunctionLevelSize H ∧
        ∀ (M : WalkingAdjunctionPoint) (a : WalkingAdjunctionCut H M)
          (_hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
            walkingAdjunctionCutRank a i)
          (_hr : ∀ i, walkingAdjunctionCutRank a i ≤
            walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i),
          (∀ i, walkingAdjunctionCutRank a i =
            walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i) ∨
          (∀ i, walkingAdjunctionCutRank a i =
            walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) := by
  rw [walkingAdjunctionLevelIsAtomic_iff_boundary_factorizations]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro M a hl hr
    rcases h (walkingAdjunctionFactorizationOfCut a hl hr) with he | he
    · left
      intro i
      have hc := congrArg (fun b : WalkingAdjunctionFactorization H =>
        walkingAdjunctionCutRank b.cut i) he
      change walkingAdjunctionCutRank (walkingAdjunctionFactorizationOfCut a hl hr).cut i =
        walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i at hc
      rw [walkingAdjunctionFactorizationOfCut_cut] at hc
      exact hc
    · right
      intro i
      have hc := congrArg (fun b : WalkingAdjunctionFactorization H =>
        walkingAdjunctionCutRank b.cut i) he
      change walkingAdjunctionCutRank (walkingAdjunctionFactorizationOfCut a hl hr).cut i =
        walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i at hc
      rw [walkingAdjunctionFactorizationOfCut_cut] at hc
      exact hc
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro a
    rcases h a.middle a.cut a.sourceCut_le a.le_targetCut with hl | hr
    · left
      apply a.ext_prefix_length (walkingAdjunctionSourceFactorization H)
      intro i
      have hc := hl i
      rw [a.cut_rank, walkingAdjunctionSourceCut_rank] at hc
      change walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
        walkingAdjunctionVertexLength X X (walkingAdjunctionIdentity X)
      rw [walkingAdjunctionVertexLength_id]
      omega
    · right
      apply a.ext_prefix_length (walkingAdjunctionTargetFactorization H)
      intro i
      have hc := hr i
      rw [a.cut_rank, walkingAdjunctionTargetCut_rank] at hc
      change walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
        walkingAdjunctionVertexLength X Y (H.obj i)
      omega

end SerrePositivity.InfinityCategories.HA.Monads
