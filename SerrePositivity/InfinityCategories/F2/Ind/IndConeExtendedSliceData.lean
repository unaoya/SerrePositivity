module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeSliceReconstruction

/-!
概要：元の q と指定 G に対する、実終点族と旧族固定円柱の全拡張データを構成する。
方針：元の二段持ち上げ、終点 comma の実拡張、三境界相対再構成を合成する。
規約：元の全係数・旧族・指定下方余錐をすべて保持し、追加の充填入力を要求しない。
使われ方：元の図式 comma の実余錐とその厳密な境界回収へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
  (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))
/-- 概要：同じ元の族に対する全終点補間と旧族固定円柱。
方針：元の実全拡張を保持。規約：全射の等号。使われ方：元の diagram comma への帰還。 -/
structure IndConeExtendedSliceData where
  initial : IndConeSliceInterpolationData κ D q G
  endpoint : join T (Δ[0] : SSet.{u + 1}) ⊗
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶
      pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D))
  prism : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⊗
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶
      sliceOver (indConeEndpointPoint κ D)
  endpoint_old : (joinInl T (Δ[0] : SSet.{u + 1}) ▷
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ endpoint = indConeEndpointRaw initial
  endpoint_lower : (join T (Δ[0] : SSet.{u + 1}) ◁
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ endpoint =
      indConeLowerEndpointRaw initial
  source : (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ prism =
      endpoint ≫ pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D))
  lower : (join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ◁
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ prism = initial.lower
  old : (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ▷
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ prism = initial.prism

/-- 概要：元の任意の小さい試験族 q と指定 G について全拡張データが存在。
方針：三つの実構成を順に適用。規約：追加の充填入力なし。使われ方：点追加の実余錐。 -/
lemma indConeExtendedSliceData_nonempty [Fact κ.IsRegular] {A : SSet.{u}}
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L) :
    Nonempty (IndConeExtendedSliceData κ D q G) := by
  obtain ⟨V⟩ := indConeSliceInterpolationData_nonempty κ D q G
  obtain ⟨E, hF, hG⟩ := exists_indConeEndpointRaw_extension κ D q G V hA hL
  obtain ⟨R, hS, hL, hO⟩ := exists_indConeSlice_reconstruction V E hF hG
  exact ⟨⟨V, E, R, hF, hG, hS, hL, hO⟩⟩
end SerrePositivity.InfinityCategories.F2.Ind
