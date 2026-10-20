module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalCartesianCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfLeftCocartesian
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfRightCartesian

/-!
概要：元の Quillen cf 対応圏の区間射影が Cartesian かつ cocartesian であることを示す。
方針：頂点を元の cf 対象として回収し、標準辺には元の置換比較、定値辺には恒等辺を使う。
規約：固定 SM7 と単体的随伴の入力を保持する。使われ方：HTT 5.2.4.6 の随伴の対応圏。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]
include fibD e SC SD in
/-- 元の左候補辺と恒等辺で全基底辺を持ち上げる、区間射影の cocartesian 性。 -/
lemma quillenCfCollageProjection_cocartesianFibration :
    CocartesianFibration (quillenCfCollageProjection R) := by
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  have := quillenCfCollageProjection_innerFibration R adj SC SD
  apply cocartesianFibration_interval_of_lift
  intro x hx
  have hlevel : (match (coherentNerveObject x).obj with
      | .inl _ => (0 : Fin 2)
      | .inr _ => 1) = 0 := by
    have hx' := hx
    rw [← coherentNerveVertex_object x, quillenCfCollageProjection_vertex] at hx'
    cases hz : (coherentNerveObject x).obj with
    | inl X => rfl
    | inr Y =>
      simp only [hz] at hx'
      exact (stdSimplex.obj₀Equiv.{max u v} (n := 1)).symm.injective hx'
  obtain ⟨X, hX⟩ := quillenCfCollage_exists_bottom_of_level_zero R
    (coherentNerveObject x) hlevel
  have hxX : x = coherentNerveVertex ((quillenCfCollageBottom R).obj X) := by
    rw [← coherentNerveVertex_object x, hX]
  rw [hxX]
  let l := SSet.yonedaEquiv.symm (quillenCfLeftLiftEdge R adj fibD X).edge
  refine ⟨l, ?_, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (quillenCfLeftLiftEdge R adj fibD X).src_eq
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      quillenCfLeftLiftEdge_projection]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  · exact quillenCfLeftLiftEdge_isCocartesian R adj fibD e SC SD X
variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))
include adj cofC SC SD in
/-- 元の右候補辺と恒等辺で全基底辺を持ち上げる、区間射影の Cartesian 性。 -/
lemma quillenCfCollageProjection_cartesianFibration :
    CartesianFibration (quillenCfCollageProjection R) := by
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  have := quillenCfCollageProjection_innerFibration R adj SC SD
  apply cartesianFibration_interval_of_lift
  intro x hx
  have hlevel : (match (coherentNerveObject x).obj with
      | .inl _ => (0 : Fin 2)
      | .inr _ => 1) = 1 := by
    have hx' := hx
    rw [← coherentNerveVertex_object x, quillenCfCollageProjection_vertex] at hx'
    cases hz : (coherentNerveObject x).obj with
    | inl X =>
      simp only [hz] at hx'
      exact (stdSimplex.obj₀Equiv.{max u v} (n := 1)).symm.injective hx'
    | inr Y => rfl
  obtain ⟨X, hX⟩ := quillenCfCollage_exists_top_of_level_one R
    (coherentNerveObject x) hlevel
  have hxX : x = coherentNerveVertex ((quillenCfCollageTop R).obj X) := by
    rw [← coherentNerveVertex_object x, hX]
  rw [hxX]
  let l := SSet.yonedaEquiv.symm (quillenCfRightLiftEdge R adj cofC X).edge
  refine ⟨l, ?_, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (quillenCfRightLiftEdge R adj cofC X).tgt_eq
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      quillenCfRightLiftEdge_projection]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  · exact quillenCfRightLiftEdge_isCartesian R adj cofC SC SD X
end
end SerrePositivity.InfinityCategories.HomotopyLimits
