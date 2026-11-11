module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseQuasicategory

/-!
概要：全ホーンの充填による Kan 性の宇宙持ち上げ。
方針：元の面の互換性を保って充填し、同じ充填単体を持ち上げる。
規約：新規の葉のみ。既存の F1 の深層モジュールは変更しない。
使われ方：元の pinched Hom のホモトピー同値の合成と相殺。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

instance kanComplex_ulift_obj (X : SSet.{u}) [KanComplex X] :
    KanComplex (SSet.uliftFunctor.{v, u}.obj X) := by
  rw [KanComplex.iff]
  intro n i f hf
  have hF : horn.IsCompatible (fun j hj ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftSimplexHomDown (f j hj)) := by
    cases n with
    | zero => trivial
    | succ n =>
      intro j k hj hk hjk
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftSimplexHomDown_face, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftSimplexHomDown_face, hf j k hj hk hjk]
  obtain ⟨φ, hφ⟩ := hF.exists_lift_of_kanComplex
  refine ⟨SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv φ)), fun j hj ↦ ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  change ULift.up (X.δ j (SSet.yonedaEquiv φ)) = SSet.yonedaEquiv (f j hj)
  apply ULift.ext
  have h := congrArg SSet.yonedaEquiv (hφ j hj)
  rw [stdSimplex.yonedaEquiv_δ_comp] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftSimplexHomDown, Equiv.apply_symm_apply] using h


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
