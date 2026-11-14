module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionPrecompWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGUniverseLiftNervePrecomposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v w))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の unlifted 比較の二段前合成は、同じ合成 dg 入力の比較に型付きで一致する。 -/
lemma dgModuleOutputResolution_unliftedPrecompIso_comp_heq
    (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (J : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A C E (H.comp J) F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A B E H (J.comp F) ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R B C E J F).precomp
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)) := by
  let UA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A)
  let UB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B)
  let UC := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)
  let hH := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
    (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B)))
  let hJ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R B).comp
    (J.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)))
  let hC := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
    ((H.comp J).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)))
  let eH := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R A B E H (J.comp F)
  let eJ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R B C E J F
  let eC := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R A C E (H.comp J) F
  let uH := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A B E H (J.comp F)
  let uJ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R B C E J F
  let outB := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R B E (J.comp F)
  let outC := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R C E F
  have hbH : UA ≫ hH = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ UB :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_sourcePrecomp_nerve.{u, v, w} R A B H
  have hbJ : UB ≫ hJ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J ≫ UC :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_sourcePrecomp_nerve.{u, v, w} R B C J
  have hbC : hH ≫ hJ = hC :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_inputPrecomp_comp_nerve.{u, v, w} R A B C H J
  have he : HEq (eC.precomp UA)
      (eH.precomp UA ≪≫ (eJ.precomp hH).precomp UA) := by
    have he0 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (eH ≪≫ eJ.precomp hH) eC rfl
      (congrArg (fun t => t ≫ outC) hbC)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso_comp_heq R A B C E H J F) UA
    exact he0.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans eH (eJ.precomp hH) UA))
  have huH := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, w} R A B E H (J.comp F)
  have huJ : HEq (uJ.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)) ((eJ.precomp hH).precomp UA) := by
    have h1 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (eJ.precomp UB) uJ rfl
      (congrArg (fun t => t ≫ outC) hbJ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, w} R B C E J F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
    have h2 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp eJ UB (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H))
    have h3 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq eJ hbH.symm
    have h4 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp eJ hH UA).symm
    exact h1.trans (h2.trans (h3.trans h4))
  have hbc : UA ≫ hH ≫ hJ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J ≫ UC := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ UB) ≫ hJ := by rw [← Category.assoc, hbH]
      _ = _ := by rw [Category.assoc, hbJ]
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_trans_heq uH (uJ.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H))
    (eH.precomp UA) ((eJ.precomp hH).precomp UA) rfl
    (congrArg (fun t => t ≫ outB) hbH.symm)
    (congrArg (fun t => t ≫ outC) hbc.symm) huH huJ
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, w} R A C E
    (H.comp J) F).trans (he.trans hp.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
