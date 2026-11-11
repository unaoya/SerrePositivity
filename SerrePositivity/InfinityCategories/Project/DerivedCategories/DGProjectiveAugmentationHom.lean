module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom
/-!
概要：元の射影的出力比較の射を、同じ augmentation の実ホモトピーの類へ同定する。
方針：端点の型輸送を除き、同じ切断と対象宇宙の上げ下げを円柱射上で照合する。
規約：比較の指定値を変更しない。使われ方：元の導来対角単位の K-flat 整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalCategory MonoidalClosed
private lemma projective_mp_heq {α β : Sort u} (h : α = β) (a : α) :
    HEq (Eq.mp h a) a := by
  cases h
  rfl
private lemma projective_mp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (Eq.mp h a) c ↔ HEq a c := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj x))
/-- 元の射影的 augmentation 同型の射は、同じ実円柱の類。 -/
lemma dgModuleAugmentationProjectiveIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationProjectiveIso R C E F hF).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F)) := by
  rfl
/-- 同じ入力切断を通る射影的出力比較の射は、同じ全単体 augmentation の類。 -/
lemma dgModuleOutputResolutionProjectiveIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso R C E F hF).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionHomotopy R C E F)) := by
  have hi : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso R C E F hF)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationProjectiveIso R C E F hF).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso]
    exact (projective_mp_heq _ _).trans (projective_mp_heq _ _)
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso R C E F hF)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationProjectiveIso R C E F hF).precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_replacement R C E F).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_original R C E F).symm hi
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_of_homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationProjectiveIso R C E F hF)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
    (dgModuleAugmentationProjectiveIso_hom R C E F hF)
  exact eq_of_heq (hh.trans ((heq_of_eq hp).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq _ _ rfl)))
/-- 元の包含比較の射は、同じ対象宇宙の上げ下げを保った resolved augmentation の類。 -/
lemma dgModuleResolvedInfinity_inclusionIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R C E F hF).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F)) := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  let e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso R C E F hF).precomp S).postcomp q
  let A := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionHomotopy R C E F) S) q
  have hi : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R C E F hF) e := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso, projective_mp_heq_iff]
    rfl
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_of_homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso R C E F hF)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionHomotopy R C E F) S
    (dgModuleOutputResolutionProjectiveIso_hom R C E F hF)
  have he : e.hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy A) := by
    simpa only [e, A, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] using!
      congrArg (fun m => (hoFunctor.map ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).map q)).toFunctor.map m) hp
  have hh : A.h = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F).h := by
    simp only [A, S, q, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionHomotopy, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy, comp_whiskerRight, Category.assoc]
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopy_endpoints_of_raw_eq A
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F) hh
  have hiHom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R C E F hF) e
    ha.1.symm ha.2.symm hi
  exact eq_of_heq (hiHom.trans ((heq_of_eq he).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F) hh)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
