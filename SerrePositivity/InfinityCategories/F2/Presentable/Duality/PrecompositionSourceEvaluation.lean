module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PrecompositionUnitEvaluation

/-!
概要：前合成の単位の Hom 対応の入口を恒等関手で評価する。
方針：転置の恒等保存と端点輸送の評価を計算し、元の右関手の恒等 Hom へ戻す。
規約：全関手圏の Hom と元の右関手を保持する。
使われ方：前合成の単位成分を元の随伴単位へ回収する入口側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：同じ両端輸送を恒等 Hom に施すと輸送先の恒等 Hom。
方針：関手の等式を除き恒等輸送を相殺する。
規約：同じ始点・終点の関手を使う。
使われ方：前合成の入口の評価の恒等射の簡約。 -/
lemma functorHomCongr_identity {A E : SSet.{u}} {U U' : A ⟶ E} (h : U = U') :
    F1B.kanFunctorHomCongr h h (𝟙 (HomotopyCategory.mk (functorVertex U))) =
      𝟙 (HomotopyCategory.mk (functorVertex U')) := by
  subst U'
  simp only [functorHomCongr_refl]

/-- 概要：元の Hom の転置は恒等 Hom を保つ。
方針：交換射が h に誘導する関手の恒等保存を使う。
規約：元の関手と転置後の関手の頂点を保持する。
使われ方：前合成の単位の入力 Hom の評価。 -/
lemma transposeHomEquiv_id {A B Z : SSet.{u}} [Quasicategory Z]
    (U : A ⟶ (ihom B).obj Z) :
    transposeHomEquiv U U (𝟙 (HomotopyCategory.mk (functorVertex U))) =
      𝟙 (HomotopyCategory.mk (functorVertex (F1B.functorTranspose U))) :=
  (hoFunctor.map (internalHomSwapIso A B Z).hom).toFunctor.map_id _

attribute [local irreducible] F1B.functorTranspose transposeHomEquiv transposeHomMap

/-- 概要：前合成の単位の入口を恒等関手で評価すると元の右関手の恒等 Hom。
方針：転置の恒等保存と始点輸送を評価し、両端の同じ輸送を相殺する。
規約：元の右関手の h Fun における恒等射を保持する。
使われ方：前合成の単位成分の回収。 -/
lemma precompositionSourceEquiv_unit_evaluate {C D : SSet.{u}} [Quasicategory C]
    (R : D ⟶ C) :
    F1B.kanFunctorHomCongr (A := D) (D := C)
      (congrArg (R ≫ ·) (transposeIdentity_evaluate C)) (transposePre_evaluate R)
      ((hoFunctor.map ((ihom D).map (identityFunctorEvaluation C))).toFunctor.map
        (precompositionSourceEquiv (Z := C) R (𝟙 ((ihom C).obj C)) ((pre R).app C)
          (𝟙 (HomotopyCategory.mk (functorVertex ((pre R).app C)))))) =
      𝟙 (HomotopyCategory.mk (functorVertex R)) := by
  dsimp only [precompositionSourceEquiv, Equiv.trans_apply]
  have hT : transposeHomEquiv (Z := C)
      ((𝟙 ((ihom C).obj C)) ≫ (pre R).app C) ((pre R).app C)
      (𝟙 (HomotopyCategory.mk (functorVertex ((pre R).app C)))) =
      𝟙 (HomotopyCategory.mk (functorVertex (F1B.functorTranspose ((pre R).app C)))) := by
    convert transposeHomEquiv_id (Z := C) ((pre R).app C) using 1 <;> rfl
  rw [hT, sourceHomTransportEquiv_eq_congr,
    ← functorHomCongr_postcomp (identityFunctorEvaluation C)
      (F1B.functorTranspose_pre_right (D := C) R (𝟙 ((ihom C).obj C))) rfl]
  let τ : FunctorHom
      (F1B.functorTranspose ((pre R).app C) ≫ identityFunctorEvaluation C)
      (F1B.functorTranspose ((pre R).app C) ≫ identityFunctorEvaluation C) :=
    (hoFunctor.map ((ihom D).map (identityFunctorEvaluation C))).toFunctor.map
      (𝟙 (HomotopyCategory.mk (functorVertex (F1B.functorTranspose ((pre R).app C)))))
  change F1B.kanFunctorHomCongr
    (congrArg (R ≫ ·) (transposeIdentity_evaluate C)) (transposePre_evaluate R)
    (F1B.kanFunctorHomCongr
      (congrArg (· ≫ identityFunctorEvaluation C)
        (F1B.functorTranspose_pre_right (D := C) R (𝟙 ((ihom C).obj C)))) rfl τ) = _
  refine (functorHomCongr_trans (A := D) (E := C)
    (congrArg (· ≫ identityFunctorEvaluation C)
      (F1B.functorTranspose_pre_right (D := C) R (𝟙 ((ihom C).obj C)))) rfl
    (congrArg (R ≫ ·) (transposeIdentity_evaluate C)) (transposePre_evaluate R) τ).trans ?_
  have hτ : τ = 𝟙 (HomotopyCategory.mk
      (functorVertex (F1B.functorTranspose ((pre R).app C) ≫ identityFunctorEvaluation C))) :=
    (hoFunctor.map ((ihom D).map (identityFunctorEvaluation C))).toFunctor.map_id _
  refine (congrArg
    (F1B.kanFunctorHomCongr
      ((congrArg (· ≫ identityFunctorEvaluation C)
        (F1B.functorTranspose_pre_right (D := C) R (𝟙 ((ihom C).obj C)))).trans
          (congrArg (R ≫ ·) (transposeIdentity_evaluate C)))
      (transposePre_evaluate R)) hτ).trans ?_
  exact functorHomCongr_identity (transposePre_evaluate R)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
