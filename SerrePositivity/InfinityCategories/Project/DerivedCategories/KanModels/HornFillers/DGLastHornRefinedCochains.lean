module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornPrecomposeCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornResidualRefinement

/-! # 追加実閉分母後の原始元から Q・A の二未知微分式へ

概要：実際に供給した cone 残差の原始元の二座標から、細分後の Q・A を取り出す。
方針：Yoneda 評価で実 cone の原始元へ戻し、第一座標の負と第二座標を読む。
規約：右辺は同じ指定 R・K の同じ閉射による前合成。使われ方：細分した実三面の充填。
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
variable {P : Set D} {σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}

/-- 最後閉辺の Yoneda 評価の各次数成分は、元の回収辺の通常順合成。 -/
lemma dgLastHornEvaluatedFinal_f (q : D) (n : ℤ)
    (f : GradedHom A q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) n) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ))).f n f =
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide)) f (add_zero n) := by
  have he := congrArg (fun t => t.f n f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ))
  have hc := (closedHomEquiv A D _ _).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalCycle σ)
  have hv : (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide) := congrArg Subtype.val hc
  exact he.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition_f A D q
    (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)) n f).trans
      (congrArg (fun t : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) 0 => compose A t f (add_zero n)) hv))

variable (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornResidualRefinement P σ)

/-- 加群 Hom の原始元を評価した、同じ最後辺の実 cone の次数 −2 の成分。 -/
def DGLastHornResidualRefinement.evaluatedPrimitive :
    ((moduleEvaluation A D H.q).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)).X (-2) :=
  (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-2)
    H.primitive

/-- 評価した成分の微分は、同じ実閉細分後の指定残差の評価そのもの。 -/
lemma DGLastHornResidualRefinement.evaluatedPrimitive_differential :
    ((moduleEvaluation A D H.q).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)).d (-2) (-1)
      H.evaluatedPrimitive =
      (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) H.s) := by
  change ((ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ)).obj (Opposite.op H.q)).d
    (-2) (-1) H.evaluatedPrimitive =
      (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) H.s)
  have hc := ConcreteCategory.congr_hom ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A H.q
    (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.comm (-2) (-1)) H.primitive
  simpa only [ModuleCat.comp_apply, H.differential_primitive,
    DGLastHornResidualRefinement.evaluatedPrimitive] using hc

/-- 同じ追加閉分母後の Q は、実 cone 原始元の第一座標の負。 -/
def DGLastHornResidualRefinement.Q : GradedHom A H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) (-1) :=
  -(mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
    ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).val.v (-2) (-1) rfl
      H.evaluatedPrimitive

/-- 同じ追加閉分母後の A は、実 cone 原始元の第二座標。 -/
def DGLastHornResidualRefinement.a : GradedHom A H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-2) :=
  (mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
    ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).v (-2) (-2) (by decide)
      H.evaluatedPrimitive

/-- 実際に回収した Q の微分は、同じ R を同じ追加閉分母で前合成したもの。 -/
lemma DGLastHornResidualRefinement.Q_differential :
    (homObject A D H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2)).d (-1) 0 H.Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingResidual σ) H.s := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_fst
    ((moduleEvaluation A D H.q).map ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))
    (-2) H.evaluatedPrimitive _ H.evaluatedPrimitive_differential
  exact hf.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPrecomposedResidual_fst σ H.q H.s)

/-- 実際に回収した A の微分は、前合成された K と最後の辺による Q の合成の和。 -/
lemma DGLastHornResidualRefinement.a_differential :
    (homObject A D H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3)).d (-2) (-1) H.a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopResidual σ) H.s +
        compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide)) H.Q (by decide) := by
  have hs : (homObject A D H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3)).d (-2) (-1) H.a =
      (mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)))).v (-1) (-1) (by decide)
        ((dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone σ))).hom.f
          (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaResidual σ) H.s)) +
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ))).f (-1) H.Q :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_snd _ (-2) H.evaluatedPrimitive _ H.evaluatedPrimitive_differential
  exact hs.trans (congrArg₂ (· + ·) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPrecomposedResidual_snd σ H.q H.s)
    (dgLastHornEvaluatedFinal_f H.q (-1) H.Q))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
