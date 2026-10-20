module
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralYonedaCoordinates
public import SerrePositivity.InfinityCategories.Derived.DGYonedaConePrecompose

/-! # 一般最後ホーン残差の閉細分後の二座標

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
variable {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 同じ実閉細分後の残差の第一座標は、元の R の前合成。 -/
lemma dgGeneralLastHornPrecomposedResidual_fst :
    (mappingCone.fst ((moduleEvaluation A D q).map
      ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)))).val.v (-(n : ℤ)) (-(n
        : ℤ) + 1) rfl
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone
        σ))).hom.f (-(n : ℤ))
        (dgRepresentableModulePrecompose A D (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ) s)) =
      dgGradedPrecompose A D (-(n : ℤ) + 1) (dgGeneralLastHornMissingResidual σ) s := by
  let x := (HornData.knownData σ).obj 0
  let g := (dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)
  let M := ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ)
  let c := (dgYonedaIso A x M).hom.f (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ)
  have he := dgRepresentableModulePrecompose_evaluation A D x q M (-(n : ℤ))
    (dgGeneralLastHornYonedaResidual σ) s
  have h₁ := congrArg ((mappingCone.fst ((moduleEvaluation A D q).map g)).val.v (-(n : ℤ))
    (-(n : ℤ) + 1) rfl) he
  have h₂ := dgModuleConeZeroAction_fst A D g x q (closedHomEquiv A D _ _ s).val (-(n : ℤ)) c
  have h₃ := dgRepresentableZeroAction A D x q ((HornData.knownData σ).obj
    (dgLastHornPenultimate n)) (-(n : ℤ) + 1)
    (closedHomEquiv A D _ _ s).val
    ((mappingCone.fst ((moduleEvaluation A D x).map g)).val.v (-(n : ℤ)) (-(n : ℤ) + 1) rfl c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => compose A t (closedHomEquiv A D _ _ s).val (zero_add (-(n : ℤ) + 1)))
      (dgGeneralLastHornYonedaResidual_fst σ))))

/-- 同じ実閉細分後の残差の第二座標は、元の K の前合成。 -/
lemma dgGeneralLastHornPrecomposedResidual_snd :
    (mappingCone.snd ((moduleEvaluation A D q).map
      ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)))).v (-(n : ℤ)) (-(n :
        ℤ)) (add_zero _)
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone
        σ))).hom.f (-(n : ℤ))
        (dgRepresentableModulePrecompose A D (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ) s)) =
      dgGradedPrecompose A D (-(n : ℤ)) (dgGeneralLastHornNormalizedK σ) s := by
  let x := (HornData.knownData σ).obj 0
  let g := (dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)
  let M := ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ)
  let c := (dgYonedaIso A x M).hom.f (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ)
  have he := dgRepresentableModulePrecompose_evaluation A D x q M (-(n : ℤ))
    (dgGeneralLastHornYonedaResidual σ) s
  have h₁ := congrArg ((mappingCone.snd ((moduleEvaluation A D q).map g)).v
    (-(n : ℤ)) (-(n : ℤ)) (add_zero _)) he
  have h₂ := dgModuleConeZeroAction_snd A D g x q (closedHomEquiv A D _ _ s).val (-(n : ℤ)) c
  have h₃ := dgRepresentableZeroAction A D x q ((HornData.knownData σ).obj (Fin.last (n +
    2))) (-(n : ℤ))
    (closedHomEquiv A D _ _ s).val
    ((mappingCone.snd ((moduleEvaluation A D x).map g)).v (-(n : ℤ)) (-(n : ℤ)) (add_zero _) c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => compose A t (closedHomEquiv A D _ _ s).val (zero_add (-(n : ℤ))))
      (dgGeneralLastHornYonedaResidual_snd σ))))

end SerrePositivity.InfinityCategories
