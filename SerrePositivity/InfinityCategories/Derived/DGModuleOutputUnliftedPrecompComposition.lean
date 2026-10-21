module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompWhisker
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftNervePrecomposition
/-!
概要：元の入力 nerve 上の指定出力比較は、二段の dg 入力前合成を保つ。
方針：同じ入力 Up を前合成し、中間の持ち上げと元の入力写像を厳密に照合する。
規約：比較の端点輸送と指定値を保持する。使われ方：元の resolved 比較の合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v w))
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
/-- 元の unlifted 比較の二段前合成は、同じ合成 dg 入力の比較に型付きで一致する。 -/
lemma dgModuleOutputResolution_unliftedPrecompIso_comp_heq
    (H : DGFunctor R A B) (J : DGFunctor R B C) (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A C E (H.comp J) F)
      (dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A B E H (J.comp F) ≪≫
        (dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R B C E J F).precomp
          (dgNerve.map H)) := by
  let UA := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A)
  let UB := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B)
  let UC := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)
  let hH := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
    (H.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B)))
  let hJ := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R B).comp
    (J.comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)))
  let hC := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
    ((H.comp J).comp (dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)))
  let eH := dgModuleOutputResolution_precompIso R A B E H (J.comp F)
  let eJ := dgModuleOutputResolution_precompIso R B C E J F
  let eC := dgModuleOutputResolution_precompIso R A C E (H.comp J) F
  let uH := dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A B E H (J.comp F)
  let uJ := dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R B C E J F
  let outB := dgModuleOutputResolutionInfinity R B E (J.comp F)
  let outC := dgModuleOutputResolutionInfinity R C E F
  have hbH : UA ≫ hH = dgNerve.map H ≫ UB :=
    dgUniverseLift_sourcePrecomp_nerve.{u, v, w} R A B H
  have hbJ : UB ≫ hJ = dgNerve.map J ≫ UC :=
    dgUniverseLift_sourcePrecomp_nerve.{u, v, w} R B C J
  have hbC : hH ≫ hJ = hC :=
    dgUniverseLift_inputPrecomp_comp_nerve.{u, v, w} R A B C H J
  have he : HEq (eC.precomp UA)
      (eH.precomp UA ≪≫ (eJ.precomp hH).precomp UA) := by
    have he0 := F2.functorIso_precomp_heq_of_heq (eH ≪≫ eJ.precomp hH) eC rfl
      (congrArg (fun t => t ≫ outC) hbC)
      (dgModuleOutputResolution_precompIso_comp_heq R A B C E H J F) UA
    exact he0.trans (heq_of_eq (F2.functorIso_precomp_trans eH (eJ.precomp hH) UA))
  have huH := dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, w} R A B E H (J.comp F)
  have huJ : HEq (uJ.precomp (dgNerve.map H)) ((eJ.precomp hH).precomp UA) := by
    have h1 := F2.functorIso_precomp_heq_of_heq (eJ.precomp UB) uJ rfl
      (congrArg (fun t => t ≫ outC) hbJ)
      (dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, w} R B C E J F)
      (dgNerve.map H)
    have h2 := heq_of_eq (F2.functorIso_precomp_precomp eJ UB (dgNerve.map H))
    have h3 := F2.functorIso_precomp_heq_of_map_eq eJ hbH.symm
    have h4 := heq_of_eq (F2.functorIso_precomp_precomp eJ hH UA).symm
    exact h1.trans (h2.trans (h3.trans h4))
  have hbc : UA ≫ hH ≫ hJ = dgNerve.map H ≫ dgNerve.map J ≫ UC := by
    calc
      _ = (dgNerve.map H ≫ UB) ≫ hJ := by rw [← Category.assoc, hbH]
      _ = _ := by rw [Category.assoc, hbJ]
  have hp := functorIso_trans_heq uH (uJ.precomp (dgNerve.map H))
    (eH.precomp UA) ((eJ.precomp hH).precomp UA) rfl
    (congrArg (fun t => t ≫ outB) hbH.symm)
    (congrArg (fun t => t ≫ outC) hbc.symm) huH huJ
  exact (dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, w} R A C E
    (H.comp J) F).trans (he.trans hp.symm)
end SerrePositivity.InfinityCategories
