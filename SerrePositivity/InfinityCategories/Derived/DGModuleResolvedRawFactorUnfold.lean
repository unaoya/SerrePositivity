module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionRawFactor
/-!
概要：元の指定 raw factor を、同じ入力切断と raw 出力射影の前合成比較へ回収する。
方針：出力の上げ下げ・同じ graph の入力前合成・指定比較の後合成を照合する。
規約：元の raw factor の値と全端点を保持。使われ方：分解変更の共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
lemma dgModuleOutputResolution_unliftedPrecompIso_Id_heq :
    HEq (dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E))) ((dgModuleOutputResolution_precompIso R C (RightModule
      R E) E F (DGFunctor.id (RightModule R E))).precomp (dgNerve.map (dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R C))) := by
  simp only [dgModuleOutputResolution_unliftedPrecompIso, Eq.mp]
  rfl
lemma dgModuleResolvedInfinity_precompIso_Id_unfold_heq :
    HEq (dgModuleResolvedInfinity_precompIso R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E))) ((dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R C
      (RightModule R E) E F (DGFunctor.id (RightModule R E))).postcomp (dgNerve.map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R E)))) := by
  simp only [dgModuleResolvedInfinity_precompIso, Eq.mp]
  rfl
lemma dgModuleResolutionLiftedInputFunctor_up_eq :
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) ≫ (dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E F)) = (dgNerve.map F) ≫ (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgUniverseLift_sourcePrecomp.{u, v, v} R C (RightModule R E) F)
  simpa only [dgModuleResolutionLiftedInputFunctor, dgNerve.map_comp, Category.assoc] using! h
end SerrePositivity.InfinityCategories
