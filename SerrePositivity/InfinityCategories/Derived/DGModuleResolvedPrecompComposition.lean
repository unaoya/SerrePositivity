module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputUnliftedPrecompComposition
/-!
概要：元の指定半自由出力分解の前合成比較は、二段の dg 入力前合成を保つ。
方針：元の unlifted 比較の合成則に同じ半自由出力 Down を後合成する。
規約：元の resolved 比較を変更しない。使われ方：raw factor の入力自然性と合成子照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の resolved 比較の二段前合成は、同じ合成 dg 入力の比較に型付きで一致する。 -/
lemma dgModuleResolvedInfinity_precompIso_comp_heq
    (H : DGFunctor R A B) (J : DGFunctor R B C) (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleResolvedInfinity_precompIso R A C E (H.comp J) F)
      (dgModuleResolvedInfinity_precompIso R A B E H (J.comp F) ≪≫
        (dgModuleResolvedInfinity_precompIso R B C E J F).precomp (dgNerve.map H)) := by
  let uH := dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A B E H (J.comp F)
  let uJ := dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R B C E J F
  let uC := dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A C E (H.comp J) F
  let rH := dgModuleResolvedInfinity_precompIso R A B E H (J.comp F)
  let rJ := dgModuleResolvedInfinity_precompIso R B C E J F
  let Dn := dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (SemifreeDGModules R E))
  let outC := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    dgModuleOutputResolutionInfinity R C E F
  have he : HEq (uC.postcomp Dn)
      ((uH.postcomp Dn) ≪≫ (uJ.postcomp Dn).precomp (dgNerve.map H)) := by
    have h1 := F2.functorIso_postcomp_heq_of_heq (uH ≪≫ uJ.precomp (dgNerve.map H)) uC rfl
      (congrArg (fun t => t ≫ outC) (dgNerve.map_comp H J).symm)
      (dgModuleOutputResolution_unliftedPrecompIso_comp_heq.{u, v, v} R A B C E H J F) Dn
    have h2 : FunctorIso.postcomp (uH ≪≫ uJ.precomp (dgNerve.map H)) Dn =
        (uH.postcomp Dn) ≪≫ (uJ.postcomp Dn).precomp (dgNerve.map H) := by
      rw [F2.functorIso_postcomp_trans, F2.functorIso_precomp_postcomp]
    exact h1.trans (heq_of_eq h2)
  have hH := dgModuleResolvedInfinity_precompIso_heq R A B E H (J.comp F)
  have hJ := F2.functorIso_precomp_heq_of_heq (uJ.postcomp Dn) rJ rfl rfl
    (dgModuleResolvedInfinity_precompIso_heq R B C E J F) (dgNerve.map H)
  have hp := functorIso_trans_heq rH (rJ.precomp (dgNerve.map H))
    (uH.postcomp Dn) ((uJ.postcomp Dn).precomp (dgNerve.map H)) rfl rfl rfl hH hJ
  exact (dgModuleResolvedInfinity_precompIso_heq R A C E (H.comp J) F).trans (he.trans hp.symm)
end SerrePositivity.InfinityCategories
