module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaConeCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornYonedaResidual

/-! # 実四次最後外ホーンの移された残差の二座標

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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 元の最後辺の後合成は、同じ Yoneda 閉射の評価と厳密に等しい。 -/
lemma dgFourLastHornPostcomposition_eq_evaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ =
      (moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition_eq_closed σ).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)).symm

/-- 実 cone 同型と Yoneda 評価の合成は、最後辺の鎖写像の等式輸送。 -/
lemma dgFourLastHornYonedaConeIso_evaluation :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaConeIso σ).hom ≫
      (dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ))).hom =
      eqToHom (congrArg (fun f : homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) ⟶
        homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4) =>
          mappingCone f) (dgFourLastHornPostcomposition_eq_evaluation σ)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaConeIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, eqToIso.hom,
    eqToHom_trans]

/-- 実四次最後ホーンの cone 同型による輸送は、Yoneda 評価の第一座標を保つ。 -/
lemma dgFourLastHornYonedaConeIso_fst (n : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).X n) :
    (mappingCone.fst ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)))).val.v n (n + 1) rfl
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ))).hom.f n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaConeIso σ).hom.f n a)) =
      (mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ)).val.v n (n + 1) rfl a := by
  have he := congrArg (fun f => f.f n a) (dgFourLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)))).val.v n (n + 1) rfl) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_fst (dgFourLastHornPostcomposition_eq_evaluation σ) n a)

/-- 実四次最後ホーンの cone 同型による輸送は、Yoneda 評価の第二座標を保つ。 -/
lemma dgFourLastHornYonedaConeIso_snd (n : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).X n) :
    (mappingCone.snd ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)))).v n n (add_zero n)
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ))).hom.f n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaConeIso σ).hom.f n a)) =
      (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ)).v n n (add_zero n) a := by
  have he := congrArg (fun f => f.f n a) (dgFourLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)))).v n n (add_zero n)) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_snd (dgFourLastHornPostcomposition_eq_evaluation σ) n a)

/-- 同じ実残差の Yoneda 評価の第一座標は、元の R。 -/
lemma dgFourLastHornYonedaResidual_fst :
    (mappingCone.fst ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)))).val.v (-2) (-1) rfl
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ))).hom.f (-2)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual σ)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ :=
  (dgFourLastHornYonedaConeIso_fst σ (-2) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual_fst σ)

/-- 同じ実残差の Yoneda 評価の第二座標は、元の K。 -/
lemma dgFourLastHornYonedaResidual_snd :
    (mappingCone.snd ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)))).v (-2) (-2) (by decide)
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone σ))).hom.f (-2)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual σ)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ :=
  (dgFourLastHornYonedaConeIso_snd σ (-2) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual_snd σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
