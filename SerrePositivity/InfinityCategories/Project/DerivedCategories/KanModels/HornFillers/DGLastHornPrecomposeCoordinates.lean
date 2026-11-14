module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornYonedaCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGYonedaConePrecompose

/-! # 実最後ホーン残差の閉細分後の二座標

概要：追加閉分母の後の指定残差の評価は、元の R・K の同じ閉射による前合成である。
方針：Yoneda 評価の自然性、加群 cone の作用、元の指定残差の二座標を照合する。
規約：始点だけを細分する。使われ方：追加分母後の原始元から Q・A を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 同じ実閉細分後の残差の第一座標は、元の R の前合成。 -/
lemma dgLastHornPrecomposedResidual_fst :
    (mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).val.v (-1) 0 rfl
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) s)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingResidual σ) s := by
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0
  let g := (dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)
  let M := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)
  let c := (dgYonedaIso A x M).hom.f (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose_evaluation A D x q M (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) s
  have h₁ := congrArg ((mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map g)).val.v (-1) 0 rfl) he
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroAction_fst A D g x q (closedHomEquiv A D _ _ s).val (-1) c
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableZeroAction A D x q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) 0
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val
    ((mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D x).map g)).val.v (-1) 0 rfl c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => _root_.SerrePositivity.DifferentialGraded.compose A t (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add (0 : ℤ)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual_fst σ))))

/-- 同じ実閉細分後の残差の第二座標は、元の K の前合成。 -/
lemma dgLastHornPrecomposedResidual_snd :
    (mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).v (-1) (-1) (by decide)
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) s)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopResidual σ) s := by
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0
  let g := (dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)
  let M := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)
  let c := (dgYonedaIso A x M).hom.f (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose_evaluation A D x q M (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) s
  have h₁ := congrArg ((mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map g)).v
    (-1) (-1) (by decide)) he
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroAction_snd A D g x q (closedHomEquiv A D _ _ s).val (-1) c
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableZeroAction A D x q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-1)
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val
    ((mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D x).map g)).v (-1) (-1) (by decide) c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => _root_.SerrePositivity.DifferentialGraded.compose A t (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add (-1 : ℤ)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual_snd σ))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
