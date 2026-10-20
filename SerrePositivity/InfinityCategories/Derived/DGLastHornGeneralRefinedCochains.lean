module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralPrecomposeCoordinates
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralResidualRefinement

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex CochainComplex HomComplex SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {n : ℕ}
variable {P : Set D} {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D}

/-- 最後閉辺の Yoneda 評価の各次数成分は、元の回収辺の通常順合成。 -/
lemma dgGeneralLastHornEvaluatedFinal_f (q : D) (k : ℤ)
    (f : GradedHom A q ((HornData.knownData σ).obj (dgLastHornPenultimate n)) k) :
    ((moduleEvaluation A D q).map ((dgYoneda A D).onClosed.map
      (dgGeneralLastHornFinalClosed σ))).f k f =
      compose A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n)) f (add_zero k) := by
  have he := congrArg (fun t => t.f k f) (dgYonedaEvaluation_postcomposition A D q
    (dgGeneralLastHornFinalClosed σ))
  have hc := (closedHomEquiv A D _ _).apply_symm_apply (dgGeneralLastHornFinalCycle σ)
  have hv : (closedHomEquiv A D _ _ (dgGeneralLastHornFinalClosed σ)).val =
      (HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n) := congrArg Subtype.val hc
  exact he.trans ((dgCyclePostcomposition_f A D q
    (closedHomEquiv A D _ _ (dgGeneralLastHornFinalClosed σ)) k f).trans
      (congrArg (fun t : GradedHom A ((HornData.knownData σ).obj (dgLastHornPenultimate n))
        ((HornData.knownData σ).obj (Fin.last (n + 2))) 0 => compose A t f (add_zero k)) hv))

variable (H : DGGeneralLastHornResidualRefinement P σ)

/-- 加群 Hom の原始元を評価した、同じ最後辺の実 cone の次数 −n−1 の成分。 -/
def DGGeneralLastHornResidualRefinement.evaluatedPrimitive :
    ((moduleEvaluation A D H.q).obj (dgGeneralLastHornYonedaCone σ)).X (-(n : ℤ) - 1) :=
  (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).hom.f
    (-(n : ℤ) - 1)
    H.primitive

/-- 評価した成分の微分は、同じ実閉細分後の指定残差の評価そのもの。 -/
lemma DGGeneralLastHornResidualRefinement.evaluatedPrimitive_differential :
    ((moduleEvaluation A D H.q).obj (dgGeneralLastHornYonedaCone σ)).d (-(n : ℤ) - 1) (-(n : ℤ))
      H.evaluatedPrimitive =
      (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone
        σ))).hom.f (-(n : ℤ))
        (dgRepresentableModulePrecompose A D (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ)
          H.s) := by
  change ((ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ)).obj (Opposite.op H.q)).d
    (-(n : ℤ) - 1) (-(n : ℤ)) H.evaluatedPrimitive =
      (dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone
        σ))).hom.f (-(n : ℤ))
        (dgRepresentableModulePrecompose A D (-(n : ℤ)) (dgGeneralLastHornYonedaResidual σ) H.s)
  have hc := ConcreteCategory.congr_hom ((dgYonedaIso A H.q
    (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).hom.comm (-(n : ℤ) -
      1) (-(n : ℤ))) H.primitive
  simpa only [ModuleCat.comp_apply, H.differential_primitive,
    DGGeneralLastHornResidualRefinement.evaluatedPrimitive] using hc

/-- 同じ追加閉分母後の Q は、実 cone 原始元の第一座標の負。 -/
def DGGeneralLastHornResidualRefinement.Q : GradedHom A H.q ((HornData.knownData σ).obj
  (dgLastHornPenultimate n)) (-(n : ℤ)) :=
  -(mappingCone.fst ((moduleEvaluation A D H.q).map
    ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)))).val.v (-(n : ℤ) - 1)
      (-(n : ℤ)) (by omega)
      H.evaluatedPrimitive

/-- 同じ追加閉分母後の A は、実 cone 原始元の第二座標。 -/
def DGGeneralLastHornResidualRefinement.a : GradedHom A H.q ((HornData.knownData σ).obj
  (Fin.last (n + 2))) (-(n : ℤ) - 1) :=
  (mappingCone.snd ((moduleEvaluation A D H.q).map
    ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)))).v (-(n : ℤ) - 1) (-(n :
      ℤ) - 1) (by omega)
      H.evaluatedPrimitive

/-- 実際に回収した Q の微分は、同じ R を同じ追加閉分母で前合成したもの。 -/
lemma DGGeneralLastHornResidualRefinement.Q_differential :
    (homObject A D H.q ((HornData.knownData σ).obj (dgLastHornPenultimate n))).d (-(n : ℤ))
      (-(n : ℤ) + 1) H.Q =
      dgGradedPrecompose A D (-(n : ℤ) + 1) (dgGeneralLastHornMissingResidual σ) H.s := by
  have hf := dgComplexConePrimitive_fst_at
    ((moduleEvaluation A D H.q).map ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)))
    (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
      H.evaluatedPrimitive _ H.evaluatedPrimitive_differential
  exact hf.trans (dgGeneralLastHornPrecomposedResidual_fst σ H.q H.s)

/-- 実際に回収した A の微分は、前合成された K と最後の辺による Q の合成の和。 -/
lemma DGGeneralLastHornResidualRefinement.a_differential :
    (homObject A D H.q ((HornData.knownData σ).obj (Fin.last (n + 2)))).d (-(n : ℤ) - 1) (-(n
      : ℤ)) H.a =
      dgGradedPrecompose A D (-(n : ℤ)) (dgGeneralLastHornNormalizedK σ) H.s +
        compose A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n)) H.Q (by omega) := by
  have hs : (homObject A D H.q ((HornData.knownData σ).obj (Fin.last (n + 2)))).d (-(n : ℤ) -
    1) (-(n : ℤ)) H.a =
      (mappingCone.snd ((moduleEvaluation A D H.q).map
        ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ)))).v (-(n : ℤ)) (-(n :
          ℤ)) (by omega)
        ((dgYonedaIso A H.q (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).hom.f
          (-(n : ℤ)) (dgRepresentableModulePrecompose A D (-(n : ℤ))
            (dgGeneralLastHornYonedaResidual σ) H.s)) +
      ((moduleEvaluation A D H.q).map
        ((dgYoneda A D).onClosed.map (dgGeneralLastHornFinalClosed σ))).f (-(n : ℤ)) H.Q :=
    dgComplexConePrimitive_snd_at _ (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
      H.evaluatedPrimitive _ H.evaluatedPrimitive_differential
  exact hs.trans (congrArg₂ (· + ·) (dgGeneralLastHornPrecomposedResidual_snd σ H.q H.s)
    (dgGeneralLastHornEvaluatedFinal_f H.q (-(n : ℤ)) H.Q))

end SerrePositivity.InfinityCategories
