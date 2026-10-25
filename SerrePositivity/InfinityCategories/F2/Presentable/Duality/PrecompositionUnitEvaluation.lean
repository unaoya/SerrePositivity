module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.TransposeHomEvaluation

/-!
概要：前合成の Hom 対応を恒等関手で評価して元の単位成分へ戻す。
方針：転置後の評価の可換性と端点輸送の合成を計算する。
規約：元の全関手圏と指定単位の Hom を保持する。
使われ方：固定左 coslice の始対象性と元の随伴単位条件の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

attribute [local irreducible] F1B.functorTranspose transposeHomEquiv transposeHomMap

/-- 概要：恒等関手を点として二重関手圏を元の圏へ評価する。
方針：元の C 上の恒等関手頂点で評価する。
規約：全ての単体に作用する元の評価射。
使われ方：前合成の単位を元の単位へ戻す評価。 -/
abbrev identityFunctorEvaluation (C : SSet.{u}) :
    (ihom ((ihom C).obj C)).obj C ⟶ C :=
  evaluateFunctorAt (Y := C) (functorVertex (𝟙 C))

/-- 概要：前合成の Hom 対応の出口を恒等関手で評価すると元の単位成分になる。
方針：端点輸送を評価の後へ移し、転置 Hom の評価公式を適用する。
規約：単位候補に随伴条件は要求しない。
使われ方：前合成随伴の単位成分の回収の出口側。 -/
lemma precompositionTargetEquiv_unit_evaluate {C D : SSet.{u}} [Quasicategory C]
    (L : C ⟶ D) (R : D ⟶ C)
    (η : FunctorHom (𝟙 ((ihom C).obj C)) ((pre R).app C ≫ (pre L).app C)) :
    F1B.kanFunctorHomCongr (A := C) (D := C) (transposeIdentity_evaluate C)
      (congrArg (L ≫ ·) (transposePre_evaluate R))
      ((hoFunctor.map ((ihom C).map (identityFunctorEvaluation C))).toFunctor.map
        (precompositionTargetEquiv (Z := C) L (𝟙 ((ihom C).obj C)) ((pre R).app C) η)) =
    qcatUnitComponent (F := (pre R).app C) (G := (pre L).app C) η
      (functorVertex (𝟙 C)) := by
  change _ = functorHomEvaluate η (functorVertex (𝟙 C))
  dsimp only [precompositionTargetEquiv, Equiv.trans_apply]
  rw [← functorHomCongr_postcomp (identityFunctorEvaluation C) rfl
    (F1B.functorTranspose_pre_right (D := C) L ((pre R).app C))]
  let τ : FunctorHom
      (F1B.functorTranspose (𝟙 ((ihom C).obj C)) ≫ identityFunctorEvaluation C)
      (F1B.functorTranspose ((pre R).app C ≫ (pre L).app C) ≫ identityFunctorEvaluation C) :=
    (hoFunctor.map ((ihom C).map (identityFunctorEvaluation C))).toFunctor.map
      (transposeHomEquiv (Z := C) (𝟙 ((ihom C).obj C)) ((pre R).app C ≫ (pre L).app C) η)
  change F1B.kanFunctorHomCongr (transposeIdentity_evaluate C)
    (congrArg (L ≫ ·) (transposePre_evaluate R))
    (F1B.kanFunctorHomCongr rfl
      (congrArg (· ≫ identityFunctorEvaluation C)
        (F1B.functorTranspose_pre_right (D := C) L ((pre R).app C))) τ) = _
  refine (functorHomCongr_trans (A := C) (E := C) rfl
    (congrArg (· ≫ identityFunctorEvaluation C)
      (F1B.functorTranspose_pre_right (D := C) L ((pre R).app C)))
    (transposeIdentity_evaluate C) (congrArg (L ≫ ·) (transposePre_evaluate R)) τ).trans ?_
  exact transposeHomEquiv_evaluate η (functorVertex (𝟙 C))

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
