module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFunctorCriterion
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridUniverse
public import SerrePositivity.InfinityCategories.Core.UniverseUniversalSquares
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafLimitDetection
public import SerrePositivity.InfinityCategories.F1.Universe.SmallSimplicialSet

/-!
概要：切除格子の表現可能前層による像で引き戻し性を検出する。
方針：元の全錐の検出定理と、標準ホーンの宇宙比較を接続する。
規約：元の圏の有限余極限や安定性を仮定しない。
使われ方：loop 同値による一般安定性判定の反対圏側の切除。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：切除の空間値標的には全ての有限形状の極限がある。
方針：各次数で有限な形状を縮小し、既存の小極限を再添字付けする。
規約：宇宙をまたぐ形状を暗黙に同一視しない。
使われ方：表現可能前層を標的とする切除判定。 -/
lemma excisionSpace_hasFiniteLimits : HasFiniteLimits SpaceInfinity.{u} where
  hasLimit {K} _ p := by
    have (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) := inferInstance
    let e := smallSimplicialSetIso.{u, u + 1} K
    obtain ⟨c, hc⟩ := hasLimit_coherentSpaceDiagram (e.hom ≫ p)
    have hd := (isLimitCone_iff_reindexIso c e.symm).mp hc
    have hp : e.inv ≫ (e.hom ≫ p) = p := by
      rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    rw [← hp]
    exact ⟨c.reindexIso e.symm, hd⟩

/-- 概要：同じ四角形の引き戻し性は全表現可能前層の像で検出できる。
方針：全錐の検出と持ち上げた標準ホーンの再添字付けを使う。
規約：表現可能前層の始域は元の反対圏の宇宙持ち上げ。
使われ方：有限極限から構成した反対圏の切除格子。 -/
lemma isPullbackSquare_iff_representablePresheafInfinity {C : SSet.{u}}
    [Quasicategory C] (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C.op) :
    IsPullbackSquare F ↔ ∀ x : C _⦋0⦌,
      IsPullbackSquare (uliftSquare.{u, u + 1} F ≫ representablePresheafInfinity x) := by
  rw [IsPullbackSquare, isLimitCone_iff_representablePresheafInfinity]
  apply forall_congr'
  intro x
  let c := mapJoinCone (representablePresheafInfinity x)
    (JoinCone.ulift.{u, u + 1} (pullbackCone F))
  let e := (uliftHornIso.{u, u + 1} 2 2).symm
  refine (isLimitCone_iff_reindexIso c e).trans ?_
  apply isLimitCone_iff_of_val_eq
  change (joinMap (𝟙 _) e.hom ≫ (JoinCone.ulift (pullbackCone F)).val) ≫
    representablePresheafInfinity x = _
  change (((JoinCone.ulift.{u, u + 1} (pullbackCone F)).reindexIso
    (uliftHornIso.{u, u + 1} 2 2).symm).val) ≫ representablePresheafInfinity x = _
  rw [pullbackCone_ulift_reindex_val]
  rfl

/-- 概要：四つの懸垂面が引き戻しなら、元の格子の入力面も引き戻しである。
方針：全表現可能前層へ格子を送り、空間値切除の結論を反映する。
規約：元の圏の有限極限を仮定せず、指定した全格子を保持する。
使われ方：有限極限だけを持つ圏の反対圏における切除。 -/
lemma excisionFullInput_isPullback_of_suspension_faces {C : SSet.{u}} [Quasicategory C]
    (F : nerve ExcisionGridIndex.{u} ⟶ C.op)
    (hF : ∀ i j : Fin 2, IsPullbackSquare (excisionGridSuspensionAt i j ≫ F)) :
    IsPullbackSquare (excisionGridSquareEmbedding ≫ F) := by
  apply (isPullbackSquare_iff_representablePresheafInfinity _).mpr
  intro x
  let := excisionSpace_hasFiniteLimits.{u}
  let G := excisionGridUniverseIso.hom ≫ (SSet.uliftFunctor.{u + 1, u}).map F ≫
    representablePresheafInfinity x
  have h := excisionFullInput_isPullback_of_raw_suspension G (by
    rintro ⟨a, b⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
    rw [excisionRawSuspensionSquare_evaluate]
    have he : excisionGridSuspensionAt i j ≫ G =
        uliftSquare.{u, u + 1} (excisionGridSuspensionAt i j ≫ F) ≫
          representablePresheafInfinity x := by
      dsimp only [G, uliftSquare]
      rw [← Category.assoc, excisionGridUniverseIso_suspension]
      simp only [Category.assoc, Functor.map_comp]
    rw [he]
    exact (isPullbackSquare_iff_representablePresheafInfinity _).mp (hF i j) x)
  have he : excisionGridSquareEmbedding ≫ G =
      uliftSquare.{u, u + 1} (excisionGridSquareEmbedding ≫ F) ≫
        representablePresheafInfinity x := by
    dsimp only [G, uliftSquare]
    rw [← Category.assoc, excisionGridUniverseIso_square]
    simp only [Category.assoc, Functor.map_comp]
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories
