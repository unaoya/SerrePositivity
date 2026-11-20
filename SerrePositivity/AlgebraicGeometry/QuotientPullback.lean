module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
概要：KST §5 の中心の逆像を、拡大イデアルによる商の Spec として計算する。
方針：Spec のファイバー積をテンソル積に移し、商とテンソル積の環同型を使う。
規約：基礎環・代数・イデアルは任意。有限性や平坦性を要求しない。
使われ方：blowup の例外閉部分スキームのチャートと Cartier 性。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

/--
概要：Spec(A/I) の Spec B 上への逆像は Spec(B/IB) と同型。
方針：アフィンスキームのファイバー積と商・テンソル積の普遍性を使う。
規約：KST §5、IB は係数写像による `Ideal.map`。
使われ方：中心のスキーム論的逆像のチャート環の同定。
-/
def specQuotientPullbackIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
        Spec (.of (B ⧸ I.map (algebraMap A B))) :=
  pullbackSpecIso A B (A ⧸ I) ≪≫
    Scheme.Spec.mapIso
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv.toCommRingCatIso.op

set_option backward.isDefEq.respectTransparency false in
/--
概要：商の Spec と逆像との同型は Spec B への包含を保つ。
方針：ファイバー積の第一射影とテンソル積の左挿入写像を計算する。
規約：KST §5、同型の逆方向と第一射影の合成を商写像で表す。
使われ方：例外イデアルの局所方程式を実際の包含射に対応させる。
-/
@[reassoc] theorem specQuotientPullbackIso_inv_fst :
    (specQuotientPullbackIso A B I).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))) := by
  unfold specQuotientPullbackIso
  simp only [Iso.trans_inv, Category.assoc]
  erw [pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  ext b
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm
    (b ⊗ₜ[A] (1 : A ⧸ I)) = Ideal.Quotient.mk _ b
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm_apply_apply
    (Ideal.Quotient.mk _ b)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
