module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PrecompositionSourceEvaluation

/-!
概要：前合成の全 QCat 随伴の単位を恒等関手で評価して元の単位を回収する。
方針：転置した Hom 対応の入口・出口の評価と Hom₁ の後合成自然性をつなぐ。
規約：元の左右の関手と指定された随伴の単位を保持する。
使われ方：固定左の普遍単位と元の随伴単位条件の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

attribute [local irreducible] F1B.functorTranspose transposeHomEquiv transposeHomMap

/-- 概要：前合成の随伴単位の恒等関手での成分は元の随伴単位。
方針：Hom 対応の単位構成を評価し、元の Hom₁ 逆対応の恒等射の公式へ戻す。
規約：元の h Fun(C,C) の指定単位を厳密に回収する。
使われ方：元の実単位に対する固定左 coslice の始対象性の証明。 -/
lemma precompositionAdjunction_unitComponent_identity {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D]
    {L : C ⟶ D} {R : D ⟶ C} (a : QCatAdjunction L R) :
    qcatUnitComponent (F := (pre R).app C) (G := (pre L).app C)
      (precompositionAdjunction (Z := C) a).unitHom (functorVertex (𝟙 C)) = a.unitHom := by
  let X := (ihom C).obj C
  let U := F1B.functorTranspose (𝟙 X)
  let V := F1B.functorTranspose ((pre R).app C)
  let k := identityFunctorEvaluation C
  let β := 𝟙 (HomotopyCategory.mk (functorVertex ((pre R).app C)))
  let η := (precompositionAdjunction (Z := C) a).unitHom
  let s := precompositionSourceEquiv (Z := C) R (𝟙 X) ((pre R).app C) β
  have hU : U ≫ k = 𝟙 C := transposeIdentity_evaluate C
  have hV : V ≫ k = R := transposePre_evaluate R
  let normalize : FunctorHom U (L ≫ V) → FunctorHom (𝟙 C) (L ≫ R) := fun γ ↦
    F1B.kanFunctorHomCongr (A := C) (D := C) hU (congrArg (L ≫ ·) hV)
      ((hoFunctor.map ((ihom C).map k)).toFunctor.map γ)
  have hη : η = precompositionTransposeEquiv (Z := C) a (𝟙 X) ((pre R).app C) β := by
    have h := precompositionAdjunction_unitHom (Z := C) a
    rw [precompositionUnitArgument (Z := C) R] at h
    exact h
  have hc := precompositionTransposeEquiv_formula (Z := C) a (𝟙 X) ((pre R).app C) β
  rw [← hη] at hc
  have he := congrArg normalize hc
  have ht : normalize (precompositionTargetEquiv (Z := C) L (𝟙 X) ((pre R).app C) η) =
      qcatUnitComponent (F := (pre R).app C) (G := (pre L).app C) η
        (functorVertex (𝟙 C)) := precompositionTargetEquiv_unit_evaluate L R η
  let σ : FunctorHom (R ≫ (U ≫ k)) (V ≫ k) :=
    (hoFunctor.map ((ihom D).map k)).toFunctor.map s
  have hm := adjointHomOneEquiv_postcomp a s k
  have hm' := congrArg (F1B.kanFunctorHomCongr hU (congrArg (L ≫ ·) hV)) hm
  have hn := adjointHomOneEquiv_congr a hU hV σ
  have hnorm := hm'.symm.trans hn
  have hs : F1B.kanFunctorHomCongr (congrArg (R ≫ ·) hU) hV σ =
      𝟙 (HomotopyCategory.mk (functorVertex R)) := precompositionSourceEquiv_unit_evaluate R
  have hlast := congrArg (adjointHomOneEquiv a (𝟙 C) R) hs
  exact ht.symm.trans
    (he.trans (hnorm.trans (hlast.trans (adjointHomOneEquiv_identity a))))

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
