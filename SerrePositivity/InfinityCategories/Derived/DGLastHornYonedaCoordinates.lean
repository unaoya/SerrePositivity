module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaConeCoordinates
public import SerrePositivity.InfinityCategories.Derived.DGLastHornYonedaResidual

/-! # 実最後外ホーンの移された残差の二座標

概要：最後閉射への二段の厳密輸送の後でも、評価の二座標は元の R・K である。
方針：二つの cone 等式輸送の座標保存と、Yoneda 同型の座標公式を合成する。
規約：同じ指定残差を保持。使われ方：追加実閉分母後の原始元の二未知式。
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
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 元の最後辺の後合成は、同じ Yoneda 閉射の評価と厳密に等しい。 -/
lemma dgLastHornPostcomposition_eq_evaluation :
    dgLastHornPostcomposition σ =
      (moduleEvaluation A D ((HornData.knownData σ).obj 0)).map
        ((dgYoneda A D).onClosed.map (dgLastHornFinalClosed σ)) :=
  (dgLastHornPostcomposition_eq_closed σ).trans
    (dgYonedaEvaluation_postcomposition A D ((HornData.knownData σ).obj 0)
      (dgLastHornFinalClosed σ)).symm

/-- 実 cone 同型と Yoneda 評価の合成は、最後辺の鎖写像の等式輸送。 -/
lemma dgLastHornYonedaConeIso_evaluation :
    (dgLastHornYonedaConeIso σ).hom ≫
      (dgYonedaIso A ((HornData.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (dgLastHornYonedaCone σ))).hom =
      eqToHom (congrArg (fun f : homObject A D ((HornData.knownData σ).obj 0)
        ((HornData.knownData σ).obj 2) ⟶
        homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) =>
          mappingCone f) (dgLastHornPostcomposition_eq_evaluation σ)) := by
  simp only [dgLastHornYonedaConeIso, dgYonedaPostcompositionConeIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, eqToIso.hom,
    eqToHom_trans]

/-- 実最後ホーンの cone 同型による輸送は、Yoneda 評価の第一座標を保つ。 -/
lemma dgLastHornYonedaConeIso_fst (n : ℤ) (a : (dgLastHornResidualCone σ).X n) :
    (mappingCone.fst ((moduleEvaluation A D ((HornData.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (dgLastHornFinalClosed σ)))).val.v n (n + 1) rfl
      ((dgYonedaIso A ((HornData.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (dgLastHornYonedaCone σ))).hom.f n
          ((dgLastHornYonedaConeIso σ).hom.f n a)) =
      (mappingCone.fst (dgLastHornPostcomposition σ)).val.v n (n + 1) rfl a := by
  have he := congrArg (fun f => f.f n a) (dgLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.fst ((moduleEvaluation A D
    ((HornData.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (dgLastHornFinalClosed σ)))).val.v n (n + 1) rfl) he).trans
        (dgConeEqToHom_fst (dgLastHornPostcomposition_eq_evaluation σ) n a)

/-- 実最後ホーンの cone 同型による輸送は、Yoneda 評価の第二座標を保つ。 -/
lemma dgLastHornYonedaConeIso_snd (n : ℤ) (a : (dgLastHornResidualCone σ).X n) :
    (mappingCone.snd ((moduleEvaluation A D ((HornData.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (dgLastHornFinalClosed σ)))).v n n (add_zero n)
      ((dgYonedaIso A ((HornData.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (dgLastHornYonedaCone σ))).hom.f n
          ((dgLastHornYonedaConeIso σ).hom.f n a)) =
      (mappingCone.snd (dgLastHornPostcomposition σ)).v n n (add_zero n) a := by
  have he := congrArg (fun f => f.f n a) (dgLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.snd ((moduleEvaluation A D
    ((HornData.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (dgLastHornFinalClosed σ)))).v n n (add_zero n)) he).trans
        (dgConeEqToHom_snd (dgLastHornPostcomposition_eq_evaluation σ) n a)

/-- 同じ実残差の Yoneda 評価の第一座標は、元の R。 -/
lemma dgLastHornYonedaResidual_fst :
    (mappingCone.fst ((moduleEvaluation A D ((HornData.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (dgLastHornFinalClosed σ)))).val.v (-1) 0 rfl
      ((dgYonedaIso A ((HornData.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (dgLastHornYonedaCone σ))).hom.f (-1)
          (dgLastHornYonedaResidual σ)) = dgLastHornMissingResidual σ :=
  (dgLastHornYonedaConeIso_fst σ (-1) (dgLastHornConeResidual σ)).trans
    (dgLastHornConeResidual_fst σ)

/-- 同じ実残差の Yoneda 評価の第二座標は、元の K。 -/
lemma dgLastHornYonedaResidual_snd :
    (mappingCone.snd ((moduleEvaluation A D ((HornData.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (dgLastHornFinalClosed σ)))).v (-1) (-1) (by decide)
      ((dgYonedaIso A ((HornData.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (dgLastHornYonedaCone σ))).hom.f (-1)
          (dgLastHornYonedaResidual σ)) = dgLastHornTopResidual σ :=
  (dgLastHornYonedaConeIso_snd σ (-1) (dgLastHornConeResidual σ)).trans
    (dgLastHornConeResidual_snd σ)

end SerrePositivity.InfinityCategories
