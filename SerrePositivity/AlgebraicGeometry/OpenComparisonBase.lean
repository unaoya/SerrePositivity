module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BlowupAffineOpenMap

/-!
概要：KST §5、Stacks 080Y の係数比較とアフィン開比較の合成の構造射公式。
方針：環と中心を固定した一般補題で二つの交換式を合成する。
規約：具体的な切断環の表示を展開せず、構造射の式だけを使う。
使われ方：一般開埋め込みの局所比較の型の正規化を抑える。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：係数環の中心比較をアフィン開比較へ合成した射は、二つの基底射の合成を持つ。
方針：比較射ごとの構造射公式と結合律を使う。
規約：KST §5、Stacks 080Y、A・B は固定された束ねた環。
使われ方：切断環を引数に持つ局所比較の効率的な基底計算。
-/
theorem centerComparison_openMap_base {X : Scheme.{u}} {A B : CommRingCat.{u}}
    (j : Spec A ⟶ X) [IsOpenImmersion j] (K : X.IdealSheafData)
    (J : Ideal B) (φ : A ⟶ B)
    (hJ : (specIdealEquiv A (K.comap j)).map φ.hom = J) :
    (affineBlowupCenterMap (specIdealEquiv A (K.comap j)) J φ.hom hJ ≫
        blowupAffineOpenMap j K) ≫ blowupπ K = affineBlowupπ J ≫ Spec.map φ ≫ j := by
  rw [Category.assoc, blowupAffineOpenMap_base, ← Category.assoc, affineBlowupCenterMap_base]
  rw [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：同じ係数環上で等しい中心の比較と開比較の合成は元の基底射を持つ。
方針：恒等係数写像の Spec が恒等射であることを関手の補題で明示する。
規約：KST §5、Stacks 080Y、関手の恒等射保存を定義的等式として扱わない。
使われ方：具体的な切断環を代入する局所構造射の計算。
-/
theorem centerComparison_id_openMap_base {X : Scheme.{u}} {A : CommRingCat.{u}}
    (j : Spec A ⟶ X) [IsOpenImmersion j] (K : X.IdealSheafData)
    (J : Ideal A) (hJ : specIdealEquiv A (K.comap j) = J) :
    (affineBlowupCenterMap (specIdealEquiv A (K.comap j)) J (RingHom.id A)
        (by rw [Ideal.map_id]; exact hJ) ≫ blowupAffineOpenMap j K) ≫ blowupπ K =
      affineBlowupπ J ≫ j := by
  rw [Category.assoc, blowupAffineOpenMap_base, ← Category.assoc, affineBlowupCenterMap_base]
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 (Spec A) := Scheme.Spec.map_id _
  rw [hid]
  exact congrArg (· ≫ j) (Category.comp_id (affineBlowupπ J))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
