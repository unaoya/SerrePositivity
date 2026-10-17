module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionValue

/-! # 外側右制限のtensor比較と残る全次数作用の可換性

## 概要
外側右制限のtensor比較と残る全次数作用の可換性。

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
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 右作用のKoszul符号は、制限前後で同じ次数積を持つ。 -/
lemma composeRightRestrictionValueIso_rightAction
    (d d' : Dᵒᵖ) (c : C) (e : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : r + p = j) (hn : i + p = n)
    (g : GradedHom A d d' p) (q : (Q.value c e).X k)
    (v : (P.value (F.obj d.unop) c).X r) :
    (composeRightRestrictionValueIso A B D C E F P Q d'.unop e).hom.f n
        (moduleAction A ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e)
          g (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d.unop) c q v ha) hn) =
      moduleAction A ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e)
        g ((composeRightRestrictionValueIso A B D C E F P Q d.unop e).hom.f i
          (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d.unop) c q v ha)) hn := by
  rw [compose_rightAction_element A D C E (Bimodule.rightRestriction A B D C F P) Q
    d d' c e ha hj hn]
  simp only [Units.smul_def, map_zsmul]
  rw [composeRightRestrictionValueIso_element, composeRightRestrictionValueIso_element]
  exact (compose_rightAction_element A B C E P Q (F.op.obj d) (F.op.obj d') c e ha hj hn
    ((F.op.map d d').f p g) q v).symm

lemma composeRightRestrictionValueIso_leftAction
    (d : D) (c : C) (e e' : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : k + p = j) (hn : i + p = n)
    (g : GradedHom A e e' p) (q : (Q.value c e).X k)
    (v : (P.value (F.obj d) c).X r) :
    (composeRightRestrictionValueIso A B D C E F P Q d e').hom.f n
        (SerrePositivity.DifferentialGraded.leftAction A
          ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).leftAt d) g
          (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d) c q v ha) hn) =
      SerrePositivity.DifferentialGraded.leftAction A
        ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).leftAt d) g
        ((composeRightRestrictionValueIso A B D C E F P Q d e).hom.f i
          (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d) c q v ha)) hn := by
  rw [compose_leftAction_element A D C E (Bimodule.rightRestriction A B D C F P) Q
    d c e e' ha hj hn, composeRightRestrictionValueIso_element,
    composeRightRestrictionValueIso_element, Bimodule.rightRestriction_leftAction,
    compose_leftAction_element A B C E P Q (F.obj d) c e e' ha hj hn]

lemma composeRightRestrictionValueIso_right_naturality (d d' : Dᵒᵖ) (e : E) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e).map d d' ≫
        homPostcompose _ (composeRightRestrictionValueIso A B D C E F P Q d'.unop e).hom =
      ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e).map d d' ≫
        homPrecompose (composeRightRestrictionValueIso A B D C E F P Q d.unop e).hom _ := by
  apply BalancedTensor.homMap_post_pre_eq A C (Q.rightAt e)
    ((Bimodule.rightRestriction A B D C F P).leftAt d.unop)
  intro p g c k r i n ha hn q v
  exact composeRightRestrictionValueIso_rightAction A B D C E F P Q d d' c e
    (j := r + p) ha rfl hn g q v

lemma composeRightRestrictionValueIso_left_naturality (d : D) (e e' : E) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).leftAt d).map e e' ≫
        homPostcompose _ (composeRightRestrictionValueIso A B D C E F P Q d e').hom =
      ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).leftAt d).map e e' ≫
        homPrecompose (composeRightRestrictionValueIso A B D C E F P Q d e).hom _ := by
  apply BalancedTensor.homMap_post_pre_eq A C (Q.rightAt e)
    ((Bimodule.rightRestriction A B D C F P).leftAt d)
  intro p g c k r i n ha hn q v
  exact composeRightRestrictionValueIso_leftAction A B D C E F P Q d c e e'
    (j := k + p) ha rfl hn g q v

end SerrePositivity.DifferentialGraded.BimoduleTensor
