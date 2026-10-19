module
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornYonedaCoordinates
public import SerrePositivity.InfinityCategories.Derived.DGYonedaConePrecompose

/-! # 実四次最後ホーン残差の閉細分後の二座標

概要：追加閉分母の後の指定残差の評価は、元の R・K の同じ閉射による前合成である。
方針：Yoneda 評価の自然性、加群 cone の作用、元の指定残差の二座標を照合する。
規約：始点だけを細分する。使われ方：追加分母後の原始元から Q・A を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex CochainComplex HomComplex SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 同じ実閉細分後の残差の第一座標は、元の R の前合成。 -/
lemma dgFourLastHornPrecomposedResidual_fst :
    (mappingCone.fst ((moduleEvaluation A D q).map
      ((dgYoneda A D).onClosed.map (dgFourLastHornFinalClosed σ)))).val.v (-2) (-1) rfl
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).hom.f (-2)
        (dgRepresentableModulePrecompose A D (-2) (dgFourLastHornYonedaResidual σ) s)) =
      dgGradedPrecompose A D (-2 + 1) (dgFourLastHornMissingResidual σ) s := by
  let x := (HornData.knownData σ).obj 0
  let g := (dgYoneda A D).onClosed.map (dgFourLastHornFinalClosed σ)
  let M := ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ)
  let c := (dgYonedaIso A x M).hom.f (-2) (dgFourLastHornYonedaResidual σ)
  have he := dgRepresentableModulePrecompose_evaluation A D x q M (-2)
    (dgFourLastHornYonedaResidual σ) s
  have h₁ := congrArg ((mappingCone.fst ((moduleEvaluation A D q).map g)).val.v (-2) (-1) rfl) he
  have h₂ := dgModuleConeZeroAction_fst A D g x q (closedHomEquiv A D _ _ s).val (-2) c
  have h₃ := dgRepresentableZeroAction A D x q ((HornData.knownData σ).obj 3) (-1)
    (closedHomEquiv A D _ _ s).val
    ((mappingCone.fst ((moduleEvaluation A D x).map g)).val.v (-2) (-1) rfl c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => compose A t (closedHomEquiv A D _ _ s).val (zero_add (-1 : ℤ)))
      (dgFourLastHornYonedaResidual_fst σ))))

/-- 同じ実閉細分後の残差の第二座標は、元の K の前合成。 -/
lemma dgFourLastHornPrecomposedResidual_snd :
    (mappingCone.snd ((moduleEvaluation A D q).map
      ((dgYoneda A D).onClosed.map (dgFourLastHornFinalClosed σ)))).v (-2) (-2) (by decide)
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).hom.f (-2)
        (dgRepresentableModulePrecompose A D (-2) (dgFourLastHornYonedaResidual σ) s)) =
      dgGradedPrecompose A D (-2) (dgFourLastHornTopResidual σ) s := by
  let x := (HornData.knownData σ).obj 0
  let g := (dgYoneda A D).onClosed.map (dgFourLastHornFinalClosed σ)
  let M := ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ)
  let c := (dgYonedaIso A x M).hom.f (-2) (dgFourLastHornYonedaResidual σ)
  have he := dgRepresentableModulePrecompose_evaluation A D x q M (-2)
    (dgFourLastHornYonedaResidual σ) s
  have h₁ := congrArg ((mappingCone.snd ((moduleEvaluation A D q).map g)).v
    (-2) (-2) (by decide)) he
  have h₂ := dgModuleConeZeroAction_snd A D g x q (closedHomEquiv A D _ _ s).val (-2) c
  have h₃ := dgRepresentableZeroAction A D x q ((HornData.knownData σ).obj 4) (-2)
    (closedHomEquiv A D _ _ s).val
    ((mappingCone.snd ((moduleEvaluation A D x).map g)).v (-2) (-2) (by decide) c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => compose A t (closedHomEquiv A D _ _ s).val (zero_add (-2 : ℤ)))
      (dgFourLastHornYonedaResidual_snd σ))))

end SerrePositivity.InfinityCategories
