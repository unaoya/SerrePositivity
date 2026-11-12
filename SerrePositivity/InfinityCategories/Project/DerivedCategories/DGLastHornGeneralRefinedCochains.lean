module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralPrecomposeCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralResidualRefinement

/-! # 追加実閉分母後の原始元から Q・A の二未知微分式へ

概要：実際に供給した cone 残差の原始元の二座標から、細分後の Q・A を取り出す。
方針：Yoneda 評価で実 cone の原始元へ戻し、第一座標の負と第二座標を読む。
規約：右辺は同じ指定 R・K の同じ閉射による前合成。使われ方：細分した一般実ホーンの充填。
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
variable {P : Set D} {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}

/-- 最後閉辺の Yoneda 評価の各次数成分は、元の回収辺の通常順合成。 -/
lemma dgGeneralLastHornEvaluatedFinal_f (q : D) (k : ℤ)
    (f : GradedHom A q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) k) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ))).f k f =
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) f (add_zero k) := by
  have he := congrArg (fun t => t.f k f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ))
  have hc := (closedHomEquiv A D _ _).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalCycle σ)
  have hv : (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n) := congrArg Subtype.val hc
  exact he.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition_f A D q
    (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)) k f).trans
      (congrArg (fun t : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) 0 => compose A t f (add_zero k)) hv))

variable (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornResidualRefinement P σ)

/-- 加群 Hom の原始元を評価した、同じ最後辺の実 cone の次数 −n−1 の成分。 -/
def DGGeneralLastHornResidualRefinement.evaluatedPrimitive :
    ((moduleEvaluation A D H.q).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ)).X (-(n : ℤ) - 1) :=
  (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.f
    (-(n : ℤ) - 1)
    H.primitive

/-- 評価した成分の微分は、同じ実閉細分後の指定残差の評価そのもの。 -/
lemma DGGeneralLastHornResidualRefinement.evaluatedPrimitive_differential :
    ((moduleEvaluation A D H.q).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ)).d (-(n : ℤ) - 1) (-(n : ℤ))
      H.evaluatedPrimitive =
      (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone
        σ))).hom.f (-(n : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual σ)
          H.s) := by
  change ((ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ)).obj (Opposite.op H.q)).d
    (-(n : ℤ) - 1) (-(n : ℤ)) H.evaluatedPrimitive =
      (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone
        σ))).hom.f (-(n : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual σ) H.s)
  have hc := ConcreteCategory.congr_hom ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A H.q
    (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.comm (-(n : ℤ) -
      1) (-(n : ℤ))) H.primitive
  simpa only [ModuleCat.comp_apply, H.differential_primitive,
    DGGeneralLastHornResidualRefinement.evaluatedPrimitive] using hc

/-- 同じ追加閉分母後の Q は、実 cone 原始元の第一座標の負。 -/
def DGGeneralLastHornResidualRefinement.Q : GradedHom A H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ)) :=
  -(mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
    ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).val.v (-(n : ℤ) - 1)
      (-(n : ℤ)) (by omega)
      H.evaluatedPrimitive

/-- 同じ追加閉分母後の A は、実 cone 原始元の第二座標。 -/
def DGGeneralLastHornResidualRefinement.a : GradedHom A H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj
  (Fin.last (n + 2))) (-(n : ℤ) - 1) :=
  (mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
    ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).v (-(n : ℤ) - 1) (-(n :
      ℤ) - 1) (by omega)
      H.evaluatedPrimitive

/-- 実際に回収した Q の微分は、同じ R を同じ追加閉分母で前合成したもの。 -/
lemma DGGeneralLastHornResidualRefinement.Q_differential :
    (homObject A D H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n))).d (-(n : ℤ))
      (-(n : ℤ) + 1) H.Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) H.s := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_fst_at
    ((moduleEvaluation A D H.q).map ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))
    (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
      H.evaluatedPrimitive _ H.evaluatedPrimitive_differential
  exact hf.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPrecomposedResidual_fst σ H.q H.s)

/-- 実際に回収した A の微分は、前合成された K と最後の辺による Q の合成の和。 -/
lemma DGGeneralLastHornResidualRefinement.a_differential :
    (homObject A D H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)))).d (-(n : ℤ) - 1) (-(n
      : ℤ)) H.a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornNormalizedK σ) H.s +
        compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) H.Q (by omega) := by
  have hs : (homObject A D H.q ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)))).d (-(n : ℤ) -
    1) (-(n : ℤ)) H.a =
      (mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)))).v (-(n : ℤ)) (-(n :
          ℤ)) (by omega)
        ((dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone σ))).hom.f
          (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (-(n : ℤ))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual σ) H.s)) +
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D H.q).map
        ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ))).f (-(n : ℤ)) H.Q :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_snd_at _ (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
      H.evaluatedPrimitive _ H.evaluatedPrimitive_differential
  exact hs.trans (congrArg₂ (· + ·) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPrecomposedResidual_snd σ H.q H.s)
    (dgGeneralLastHornEvaluatedFinal_f H.q (-(n : ℤ)) H.Q))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
