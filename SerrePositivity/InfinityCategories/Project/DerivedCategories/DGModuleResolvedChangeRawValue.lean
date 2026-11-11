module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputResolutionRawChange
/-!
概要：元の出力分解と変更同型の指定値を、同じ raw 出力射影へ回収する。
方針：出力宇宙の上げ下げと指定出力比較の後合成則だけを使う。
規約：元の入力切断と変更比較を保持。使われ方：導来射作用との共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
  (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
lemma dgModuleResolvedInfinity_changeIso_unfold_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso R C E a hs hq ha)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso R C E a hs hq ha).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso, Eq.mp]
  rfl
lemma dgModuleResolvedInfinity_changeIso_raw_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso R C E a hs hq ha)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) := by
  have h₀ := dgModuleResolvedInfinity_changeIso_unfold_heq R C E a hs hq ha
  have h₁ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso R C E a hs hq ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))))
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawChangeIso R C E a hs hq ha)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso R C E a hs hq ha).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_down_eq R C E F).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_down_eq R C E G).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso_down_heq R C E a hs hq ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  exact h₀.trans (h₁.trans h₂)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
