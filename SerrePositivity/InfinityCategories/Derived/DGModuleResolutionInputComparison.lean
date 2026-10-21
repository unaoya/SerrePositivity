module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionPrecomp
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionStrictCounit
public import SerrePositivity.InfinityCategories.Derived.ResolutionStrictCounitComparison
/-!
概要：元の出力分解の前合成比較に使う、同じ実入力比較を明示する。
方針：元の入力射影を用い、指定余単位の厳密な式で基底像を正規化する。
規約：別の入力比較を選ばない。使われ方：元の augmentation と出力比較の正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 同じ二つの厳密入力切断と実前合成 dg 関手の間の、元の指定入力比較。 -/
def dgModuleResolutionPrecompSourceIso :
    FunctorIso
      ((dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)).inv ≫
        dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F))
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) := by
  have hs := congrArg (fun G => dgNerve.map G)
    (dgModuleResolutionPrecompFunctor_sourceLift R A C E H F)
  simp only [dgNerve.map_comp] at hs
  exact qCatResolutionSourceComparisonIso
    (dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F))
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    _ (dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)) hs
/-- 同じ指定入力比較を実入力射影で写すと、同じ基底射の恒等同型になる。 -/
lemma dgModuleResolutionPrecompSourceIso_postcomp_source_heq :
    HEq ((dgModuleResolutionPrecompSourceIso R A C E H F).postcomp
      (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F)))
      (Iso.refl (HomotopyCategory.mk (functorVertex
        (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
          (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))))))) := by
  unfold dgModuleResolutionPrecompSourceIso
  exact qCatResolutionSourceComparisonIso_strict_postcomp_heq _ _ _ _ _
    (dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R A E (H.comp F))
    (dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R C E F)
    (dgModuleFunctorResolutionSourceNerveEquivalence_invHomIso R A E (H.comp F))
    (dgModuleFunctorResolutionSourceNerveEquivalence_invHomIso R C E F)
/-- 元の実出力比較は、同じ指定入力比較を実半自由出力射影で写したものである。 -/
lemma dgModuleOutputResolution_precompIso_sourceComparison_heq :
    HEq (dgModuleOutputResolution_precompIso R A C E H F)
      ((dgModuleResolutionPrecompSourceIso R A C E H F).postcomp
        (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F))) := by
  unfold dgModuleOutputResolution_precompIso dgModuleResolutionPrecompSourceIso
  exact qCatResolutionOutputPrecompIso_sourceComparison_heq _ _ _ _ _ _ _ _
end SerrePositivity.InfinityCategories
