module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGYonedaConeCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornGeneralYonedaResidual

/-! # 一般最後外ホーンの移された残差の二座標

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
variable {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 元の最後辺の後合成は、同じ Yoneda 閉射の評価と厳密に等しい。 -/
lemma dgGeneralLastHornPostcomposition_eq_evaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ =
      (moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition_eq_closed σ).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)).symm

/-- 実 cone 同型と Yoneda 評価の合成は、最後辺の鎖写像の等式輸送。 -/
lemma dgGeneralLastHornYonedaConeIso_evaluation :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaConeIso σ).hom ≫
      (dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom =
      eqToHom (congrArg (fun f : homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) ⟶
        homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n
          + 2))) =>
          mappingCone f) (dgGeneralLastHornPostcomposition_eq_evaluation σ)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaConeIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, eqToIso.hom,
    eqToHom_trans]

/-- 一般最後ホーンの cone 同型による輸送は、Yoneda 評価の第一座標を保つ。 -/
lemma dgGeneralLastHornYonedaConeIso_fst (k : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).X k) :
    (mappingCone.fst ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).val.v k (k + 1) rfl
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.f k
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaConeIso σ).hom.f k a)) =
      (mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)).val.v k (k + 1) rfl a := by
  have he := congrArg (fun f => f.f k a) (dgGeneralLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).val.v k (k + 1) rfl) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_fst (dgGeneralLastHornPostcomposition_eq_evaluation σ) k a)

/-- 一般最後ホーンの cone 同型による輸送は、Yoneda 評価の第二座標を保つ。 -/
lemma dgGeneralLastHornYonedaConeIso_snd (k : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).X k) :
    (mappingCone.snd ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).v k k (add_zero k)
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.f k
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaConeIso σ).hom.f k a)) =
      (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)).v k k (add_zero k) a := by
  have he := congrArg (fun f => f.f k a) (dgGeneralLastHornYonedaConeIso_evaluation σ)
  exact (congrArg ((mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map ((dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).v k k (add_zero k)) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_snd (dgGeneralLastHornPostcomposition_eq_evaluation σ) k a)

/-- 同じ実残差の Yoneda 評価の第一座標は、元の R。 -/
lemma dgGeneralLastHornYonedaResidual_fst :
    (mappingCone.fst ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).val.v (-(n : ℤ)) (-(n
        : ℤ) + 1) rfl
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.f (-(n : ℤ))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual σ)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ :=
  (dgGeneralLastHornYonedaConeIso_fst σ (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual_fst σ)

/-- 同じ実残差の Yoneda 評価の第二座標は、元の K。 -/
lemma dgGeneralLastHornYonedaResidual_snd :
    (mappingCone.snd ((moduleEvaluation A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)).map
      ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).v (-(n : ℤ)) (-(n :
        ℤ)) (add_zero _)
      ((dgYonedaIso A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.f (-(n : ℤ))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual σ)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornNormalizedK σ :=
  (dgGeneralLastHornYonedaConeIso_snd σ (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual_snd σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
