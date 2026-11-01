module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalCategory MonoidalClosed
private lemma projective_mp_heq {α β : Sort u} (h : α = β) (a : α) :
    HEq (Eq.mp h a) a := by
  cases h
  rfl
private lemma projective_mp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (Eq.mp h a) c ↔ HEq a c := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (hF : ∀ x, dgModuleProjectiveProperty R E (F.obj x))
/-- 元の射影的 augmentation 同型の射は、同じ実円柱の類。 -/
lemma dgModuleAugmentationProjectiveIso_hom :
    (dgModuleAugmentationProjectiveIso R C E F hF).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgModuleAugmentationNerveHomotopy R C E F)) := by
  rfl
/-- 同じ入力切断を通る射影的出力比較の射は、同じ全単体 augmentation の類。 -/
lemma dgModuleOutputResolutionProjectiveIso_hom :
    (dgModuleOutputResolutionProjectiveIso R C E F hF).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgModuleOutputResolutionHomotopy R C E F)) := by
  have hi : HEq (dgModuleOutputResolutionProjectiveIso R C E F hF)
      ((dgModuleAugmentationProjectiveIso R C E F hF).precomp
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) := by
    simp only [dgModuleOutputResolutionProjectiveIso]
    exact (projective_mp_heq _ _).trans (projective_mp_heq _ _)
  have hh := functorIso_hom_heq (dgModuleOutputResolutionProjectiveIso R C E F hF)
    ((dgModuleAugmentationProjectiveIso R C E F hF).precomp
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)
    (dgModuleOutputResolution_replacement R C E F).symm
    (dgModuleOutputResolution_original R C E F).symm hi
  have hp := functorIso_precomp_hom_of_homotopy
    (dgModuleAugmentationProjectiveIso R C E F hF)
    (dgModuleAugmentationNerveHomotopy R C E F)
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
    (dgModuleAugmentationProjectiveIso_hom R C E F hF)
  exact eq_of_heq (hh.trans ((heq_of_eq hp).trans
    (functorHomotopyHom_heq_of_raw_eq _ _ rfl)))
/-- 元の包含比較の射は、同じ対象宇宙の上げ下げを保った resolved augmentation の類。 -/
lemma dgModuleResolvedInfinity_inclusionIso_hom :
    (dgModuleResolvedInfinity_inclusionIso R C E F hF).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgModuleResolvedAugmentationHomotopy R C E F)) := by
  let S := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let q := dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (RightModule R E))
  let e := ((dgModuleOutputResolutionProjectiveIso R C E F hF).precomp S).postcomp q
  let A := functorHomotopyPostcomp
    (functorHomotopyPrecomp (dgModuleOutputResolutionHomotopy R C E F) S) q
  have hi : HEq (dgModuleResolvedInfinity_inclusionIso R C E F hF) e := by
    simp only [dgModuleResolvedInfinity_inclusionIso, projective_mp_heq_iff]
    rfl
  have hp := functorIso_precomp_hom_of_homotopy
    (dgModuleOutputResolutionProjectiveIso R C E F hF)
    (dgModuleOutputResolutionHomotopy R C E F) S
    (dgModuleOutputResolutionProjectiveIso_hom R C E F hF)
  have he : e.hom = Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy A) := by
    simpa only [e, A, F2.functorIso_postcomp_hom, functorHomotopyPostcomp_hom] using!
      congrArg (fun m => (hoFunctor.map ((ihom (dgNerve R C)).map q)).toFunctor.map m) hp
  have hh : A.h = (dgModuleResolvedAugmentationHomotopy R C E F).h := by
    simp only [A, S, q, functorHomotopyPrecomp, functorHomotopyPostcomp,
      dgModuleOutputResolutionHomotopy, dgModuleResolvedAugmentationHomotopy,
      dgModuleAugmentationUnliftedHomotopy, comp_whiskerRight, Category.assoc]
  have ha := functorHomotopy_endpoints_of_raw_eq A
    (dgModuleResolvedAugmentationHomotopy R C E F) hh
  have hiHom := functorIso_hom_heq (dgModuleResolvedInfinity_inclusionIso R C E F hF) e
    ha.1.symm ha.2.symm hi
  exact eq_of_heq (hiHom.trans ((heq_of_eq he).trans
    (functorHomotopyHom_heq_of_raw_eq A (dgModuleResolvedAugmentationHomotopy R C E F) hh)))
end SerrePositivity.InfinityCategories
