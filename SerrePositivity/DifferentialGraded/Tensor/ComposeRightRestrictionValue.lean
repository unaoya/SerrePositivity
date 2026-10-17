module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestrictionLeftEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.LeftColimits
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # 外側右作用制限と相対tensor合成の値の比較

## 概要
外側右作用制限と相対tensor合成の値の比較。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 外側の右作用を制限してから合成した値を、合成後に制限した値へ送る同型。 -/
def composeRightRestrictionValueIso (P : Bimodule A B C) (Q : Bimodule A C E) (d : D) (e : E) :
    (compose A D C E (Bimodule.rightRestriction A B D C F P) Q).value d e ≅
      (compose A B C E P Q).value (F.obj d) e :=
  (BalancedTensor.leftTensorFunctor A C (Q.rightAt e)).mapIso
    (Bimodule.rightRestrictionLeftEvaluationIso A B D C F (BimoduleCategory.of A B C P) d)

@[reassoc]
lemma ι_composeRightRestrictionValueIso_hom (P : Bimodule A B C) (Q : Bimodule A C E)
    (d : D) (e : E) (c : C) :
    BalancedTensor.ι A C (Q.rightAt e) ((Bimodule.rightRestriction A B D C F P).leftAt d) c ≫
        (composeRightRestrictionValueIso A B D C E F P Q d e).hom =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt (F.obj d)) c := by
  change BalancedTensor.ι A C (Q.rightAt e)
      ((Bimodule.rightRestriction A B D C F P).leftAt d) c ≫
      BalancedTensor.map A C (𝟙 (ForgetEnrichment.of (Complex A) (Q.rightAt e)))
        (Bimodule.rightRestrictionLeftEvaluationIso A B D C F
          (BimoduleCategory.of A B C P) d).hom = _
  have h := BalancedTensor.ι_map A C
    (M := ForgetEnrichment.of (Complex A) (Q.rightAt e))
    (M' := ForgetEnrichment.of (Complex A) (Q.rightAt e))
    (N := (BimoduleCategory.leftEvaluation A D C d).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj
        (BimoduleCategory.of A B C P)))
    (N' := (BimoduleCategory.leftEvaluation A B C (F.obj d)).obj
      (BimoduleCategory.of A B C P))
    (𝟙 (ForgetEnrichment.of (Complex A) (Q.rightAt e)))
    (Bimodule.rightRestrictionLeftEvaluationIso A B D C F
      (BimoduleCategory.of A B C P) d).hom c
  simp only [CategoryTheory.Functor.map_id,
    Bimodule.rightRestrictionLeftEvaluationIso_hom_eval, tensorHom_id, id_whiskerRight] at h
  exact h.trans (Category.id_comp (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt (F.obj d)) c))

lemma composeRightRestrictionValueIso_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (d : D) (c : C) (e : E) {r s n : ℤ} (hn : r + s = n)
    (q : (Q.value c e).X r) (p : (P.value (F.obj d) c).X s) :
    (composeRightRestrictionValueIso A B D C E F P Q d e).hom.f n
        (BalancedTensor.element A C (Q.rightAt e)
          ((Bimodule.rightRestriction A B D C F P).leftAt d) c q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt (F.obj d)) c q p hn :=
  BalancedTensor.element_postcompose A C (Q.rightAt e)
    ((Bimodule.rightRestriction A B D C F P).leftAt d) c _ _
    (ι_composeRightRestrictionValueIso_hom A B D C E F P Q d e c) q p hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
