module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFunctorCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridUniverse
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseUniversalSquares
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentablePresheafLimitDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialSet

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：切除の空間値標的には全ての有限形状の極限がある。
方針：各次数で有限な形状を縮小し、既存の小極限を再添字付けする。
規約：宇宙をまたぐ形状を暗黙に同一視しない。
使われ方：表現可能前層を標的とする切除判定。 -/
lemma excisionSpace_hasFiniteLimits : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  hasLimit {K} _ p := by
    have (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) := inferInstance
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} K
    obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasLimit_coherentSpaceDiagram (e.hom ≫ p)
    have hd := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso c e.symm).mp hc
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ ∀ x : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, u + 1} F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_representablePresheafInfinity]
  apply forall_congr'
  intro x
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F))
  let e := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, u + 1} 2 2).symm
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso c e).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_of_val_eq
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)).val) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x = _
  change (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)).reindexIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, u + 1} 2 2).symm).val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pullbackCone_ulift_reindex_val]
  rfl

/-- 概要：四つの懸垂面が引き戻しなら、元の格子の入力面も引き戻しである。
方針：全表現可能前層へ格子を送り、空間値切除の結論を反映する。
規約：元の圏の有限極限を仮定せず、指定した全格子を保持する。
使われ方：有限極限だけを持つ圏の反対圏における切除。 -/
lemma excisionFullInput_isPullback_of_suspension_faces {C : SSet.{u}} [Quasicategory C]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ C.op)
    (hF : ∀ i j : Fin 2, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ F) := by
  apply (isPullbackSquare_iff_representablePresheafInfinity _).mpr
  intro x
  let := excisionSpace_hasFiniteLimits.{u}
  let G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUniverseIso.hom ≫ (SSet.uliftFunctor.{u + 1, u}).map F ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInput_isPullback_of_raw_suspension G (by
    rintro ⟨a, b⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_evaluate]
    have he : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ G =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ F) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x := by
      dsimp only [G, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUniverseIso_suspension]
      simp only [Category.assoc, Functor.map_comp]
    rw [he]
    exact (isPullbackSquare_iff_representablePresheafInfinity _).mp (hF i j) x)
  have he : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ G =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x := by
    dsimp only [G, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUniverseIso_square]
    simp only [Category.assoc, Functor.map_comp]
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "6.1.1.6" (partial := special) "仮定：C=S を構成済みの空間 ∞ 圏に限定（Lean が強い：空間の場合）。結論：有限極限が存在し、選んだ全小余極限関手のうち filtered 添字のものは全有限極限錐を保つ。特に順序添字で differentiable の三条件を満たす（この場合の定義条件に一致）。任意 C に対する differentiable の専用述語は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSpace_hasFiniteLimits
attribute [cite HA "6.1.1.8" (partial := special) "仮定：∞ トポスを S の場合に限定（Lean が強い：構成済みの空間 ∞ 圏の場合）。結論：有限極限と全小余極限が存在し、filtered 余極限関手が全有限極限を保つので順序余極限も左完全（S が differentiable という結論に一致）。一般 ∞ トポスの切除と filtered exactness の主張は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSpace_hasFiniteLimits
