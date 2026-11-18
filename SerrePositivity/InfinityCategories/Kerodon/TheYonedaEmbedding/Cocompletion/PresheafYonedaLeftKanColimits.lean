module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafExtensionHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoYonedaLimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.UniverseCoconePostcomposition

/-!
概要：全前層 Yoneda の左 Kan 延長が、任意の小さい指定余極限を保存することを示す。
方針：既存の全 Hom 係数の大域的右 Kan 比較で極限性を移し、co-Yoneda と宇宙変更で反映する。
規約：形状に sifted 性を要求せず、元の全余錐と指定した左 Kan 単位を保持する。
使われ方：HTT 5.1.5.6、Kerodon §8.4（Tag 03V7）、S8 の全重み切断の連続性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ E} {L : PresheafInfinity A ⟶ E}
  (β : SSet.Homotopy F₀ (yonedaInfinityMap A ≫ L))
  (hβ : IsLeftKanExtension (yonedaInfinityMap A) F₀ L β)

include β hβ in
/-- 全前層 Yoneda の左 Kan 延長は、任意の小さい形状の同じ指定余錐を余極限へ送る。
HTT 5.1.5.6、Kerodon §8.4（Tag 03V7）。既存の全 Hom の大域的比較と極限判定を用いる。 -/
lemma presheafYonedaLeftKan_map_isColimit {I : SSet.{u}}
    {p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafInfinity A}
    (c : JoinCocone p) (hc : IsColimitCone c) : IsColimitCone (mapJoinCocone L c) := by
  let d := JoinCocone.ulift.{u + 1, u + 2} c
  have h := fullPresheafHomWeightFamily_map_isLimit F₀ p c hc
  have h' : IsLimitCone (mapJoinCone (canonicalLiftedHomFamily L)
      (JoinCone.ulift.{u + 2, u + 3} (coconeReverseCone d))) :=
    h.of_functorIso ((presheafExtensionHom_liftedIso β hβ).precomp
      (JoinCone.ulift.{u + 2, u + 3} (coconeReverseCone d)).val)
  unfold canonicalLiftedHomFamily at h'
  rw [mapJoinCone_universe_comp] at h'
  have hlim := coyonedaInfinityMap_reflects_isLimit _ h'
  have hcol := (isLimitCone_reverse_postcomp_iff d
    ((SSet.uliftFunctor.{u + 2, u + 1}).map L)).mp hlim
  apply (isColimitCone_iff_ulift (mapJoinCocone L c)).mpr
  apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hcol
  exact (ulift_mapJoinCocone_val L c).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
