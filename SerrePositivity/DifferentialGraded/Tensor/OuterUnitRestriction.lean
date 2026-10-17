module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeLeftRestriction
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestriction
public import SerrePositivity.DifferentialGraded.Tensor.UnitMapNaturality

/-! # 外側だけを制限した合成比較と対角の単位子

## 概要
外側だけを制限した合成比較と対角の単位子。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory

section Left
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] (D : Type z) [DGCategory A D] (F : DGFunctor A D C)
  (Q : BimoduleCategory A B C)

lemma leftUnitValue_leftRestriction (b : B) (d : D) :
    (leftUnitValueIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C Q)) b d).hom =
    (leftUnitValueIso A B C (BimoduleCategory.underlying A B C Q) b (F.obj d)).hom := rfl

/-- 外側左制限比較と左単位子の可換square。C・Dのsmallnessは不要。 -/
lemma leftBimoduleUnitIso_leftRestriction :
    (composeLeftRestrictionIso A B B C D F
        (BimoduleCategory.of A B B (Bimodule.diagonal A B)) Q).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C Q)).hom =
    (leftBimoduleUnitIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C Q))).hom := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeLeftRestrictionIso_hom_value]
  rw [Category.id_comp]
  erw [BimoduleCategory.middleLeftRestrictionMap_value_eval,
    leftBimoduleUnitIso_hom_value]
end Left

section Right
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C)

/-- 右制限での左加群表示のYoneda自然性から、値での右単位squareを得る。 -/
lemma rightUnitValue_rightRestriction (d : D) (c : C) :
    (composeRightRestrictionValueIso A B D C C F (BimoduleCategory.underlying A B C P)
        (Bimodule.diagonal A C) d c).hom ≫
      (rightUnitValueIso A B C (BimoduleCategory.underlying A B C P) (F.obj d) c).hom =
    (rightUnitValueIso A D C
      (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P)) d c).hom := by
  have h := BalancedTensor.yonedaEvaluation_naturality A C c
    (Bimodule.rightRestrictionLeftEvaluationIso A B D C F P d).hom
  rw [Bimodule.rightRestrictionLeftEvaluationIso_hom_eval] at h
  erw [Category.comp_id] at h
  exact h

/-- 外側右制限比較と右単位子の可換square。Fの準同値性・局所Hom条件は不要。 -/
lemma rightBimoduleUnitIso_rightRestriction :
    (composeRightRestrictionIso A B D C C F P
        (BimoduleCategory.of A C C (Bimodule.diagonal A C))).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (rightBimoduleUnitIso A D C
      (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P))).hom := by
  apply BimoduleCategory.value_hom_ext A D C
  intro d c
  simp only [CategoryTheory.Functor.map_comp, composeRightRestrictionIso_hom_value]
  have he := BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F
    (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom d c
  have hu := rightBimoduleUnitIso_hom_value A B C
    (BimoduleCategory.underlying A B C P) (F.obj d) c
  have hv := rightBimoduleUnitIso_hom_value A D C
    (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P)) d c
  exact (congrArg (fun k =>
    (composeRightRestrictionValueIso A B D C C F (BimoduleCategory.underlying A B C P)
      (Bimodule.diagonal A C) d c).hom ≫ k) (he.trans hu)).trans
    ((rightUnitValue_rightRestriction A B D C F P d c).trans hv.symm)
end Right

end SerrePositivity.DifferentialGraded.BimoduleTensor
