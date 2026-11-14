module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGYonedaConeCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornYonedaResidual

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 元の最後辺の後合成は、同じ Yoneda 閉射の評価と厳密に等しい。 -/
lemma dgLastHornPostcomposition_eq_evaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPostcomposition σ =
      (moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPostcomposition_eq_closed σ).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)).symm

/-- 実 cone 同型と Yoneda 評価の合成は、最後辺の鎖写像の等式輸送。 -/
lemma dgLastHornYonedaConeIso_evaluation :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaConeIso σ).hom ≫
      (dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom =
      eqToHom (congrArg (fun f : homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) ⟶
        homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) =>
          mappingCone f) (dgLastHornPostcomposition_eq_evaluation σ)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaConeIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, eqToIso.hom,
    eqToHom_trans]

/-- 実最後ホーンの cone 同型による輸送は、Yoneda 評価の第一座標を保つ。 -/
lemma dgLastHornYonedaConeIso_fst (n : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornResidualCone σ).X n) :
    (mappingCone.fst ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).val.v n (n + 1) rfl
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaConeIso σ).hom.f n a)) =
      (mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPostcomposition σ)).val.v n (n + 1) rfl a := by
  have he := congrArg (fun f => f.f n a) (dgLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).val.v n (n + 1) rfl) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_fst (dgLastHornPostcomposition_eq_evaluation σ) n a)

/-- 実最後ホーンの cone 同型による輸送は、Yoneda 評価の第二座標を保つ。 -/
lemma dgLastHornYonedaConeIso_snd (n : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornResidualCone σ).X n) :
    (mappingCone.snd ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).v n n (add_zero n)
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaConeIso σ).hom.f n a)) =
      (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPostcomposition σ)).v n n (add_zero n) a := by
  have he := congrArg (fun f => f.f n a) (dgLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).v n n (add_zero n)) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_snd (dgLastHornPostcomposition_eq_evaluation σ) n a)

/-- 同じ実残差の Yoneda 評価の第一座標は、元の R。 -/
lemma dgLastHornYonedaResidual_fst :
    (mappingCone.fst ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).val.v (-1) 0 rfl
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingResidual σ :=
  (dgLastHornYonedaConeIso_fst σ (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual σ)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual_fst σ)

/-- 同じ実残差の Yoneda 評価の第二座標は、元の K。 -/
lemma dgLastHornYonedaResidual_snd :
    (mappingCone.snd ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).v (-1) (-1) (by decide)
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopResidual σ :=
  (dgLastHornYonedaConeIso_snd σ (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual σ)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual_snd σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
