module

public import SerrePositivity.AlgebraicGeometry.AffineIdealPullback
public import SerrePositivity.AlgebraicGeometry.SchemeBlowup

/-!
概要：KST §5、Stacks 080Y の任意のアフィン開埋め込みから一般 blowup への比較射。
方針：開像の切断環への Spec の同型を使い、係数環の中心比較射を一般の局所モデルへ送る。
規約：チャート環と開像の切断環を定義的に同一視しない。
使われ方：実際のチャート環の局所的可逆性から一般 blowup への持ち上げを作る。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]

/--
概要：アフィン開埋め込みの像を基底のアフィン開集合として束ねる。
方針：アフィンスキームの開埋め込み像のアフィン性を使う。
規約：KST §5、Stacks 080Y、与えられたチャート射を保持する。
使われ方：全アフィン開集合上の blowup 局所モデルへの接続。
-/
def affineOpenImage : X.affineOpens := ⟨j.opensRange, isAffineOpen_opensRange j⟩

set_option backward.isDefEq.respectTransparency false in
/--
概要：与えられたアフィンチャートと、その開像の切断環の Spec の実際の同型。
方針：基底への二つの開埋め込みの像が等しいことを使う。
規約：KST §5、Stacks 080Y、基底への射を保つ同型。
使われ方：チャート環から開像の切断環への係数写像。
-/
def affineOpenImageSpecIso : Spec A ≅ Spec Γ(X, (affineOpenImage j).1) := by
  apply IsOpenImmersion.isoOfRangeEq j (affineOpenImage j).2.fromSpec
  change (j.opensRange : Set X) = ((affineOpenImage j).2.fromSpec.opensRange : Set X)
  rw [(affineOpenImage j).2.opensRange_fromSpec]
  rfl

/--
概要：開像の切断環から元のチャート環への係数環準同型。
方針：Spec の同型の順方向の環準同型を取り出す。
規約：KST §5、Stacks 080Y、環の表示の違いを明示する。
使われ方：通常 blowup の係数比較射の入力。
-/
def affineOpenImageRingMap : Γ(X, (affineOpenImage j).1) ⟶ A :=
  Spec.preimage (affineOpenImageSpecIso j).hom

set_option backward.isDefEq.respectTransparency false in
/--
概要：開像の係数写像の Spec は基底への元のチャート射を与える。
方針：Spec の充満忠実性と開像同型の因子化式を使う。
規約：KST §5、Stacks 080Y、実際の基底上の等式。
使われ方：中心の像イデアルと構造射の比較。
-/
@[reassoc] theorem affineOpenImageRingMap_spec_base :
    Spec.map (affineOpenImageRingMap j) ≫ (affineOpenImage j).2.fromSpec = j := by
  rw [affineOpenImageRingMap, Spec.map_preimage]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac ..

variable (K : X.IdealSheafData)

/--
概要：開像の切断中心を係数環へ拡大すると実際の逆像チャートイデアルになる。
方針：任意のアフィン局所射の逆像公式と係数写像の基底交換式を使う。
規約：KST §5、Stacks 080Y、中心のスキーム構造を保持する。
使われ方：任意のアフィン開埋め込み上の blowup の中心比較。
-/
theorem affineOpenImageRingMap_center :
    (K.ideal (affineOpenImage j)).map (affineOpenImageRingMap j).hom =
      specIdealEquiv A (K.comap j) := by
  rw [← specIdealEquiv_comap_affine_local K (affineOpenImage j) A (affineOpenImageRingMap j),
    affineOpenImageRingMap_spec_base]

/--
概要：任意のアフィン開チャート上の通常 blowup から一般の blowup への実際の比較射。
方針：係数環の中心比較射と開像の局所モデルの標準射を合成する。
規約：KST §5、Stacks 080Y、始域中心は実際の逆像イデアル層に対応する環イデアル。
使われ方：チャート上で構成した普遍写像を一般基底へ送る。
-/
def blowupAffineOpenMap : affineBlowup (specIdealEquiv A (K.comap j)) ⟶ blowup K :=
  affineBlowupCenterMap (K.ideal (affineOpenImage j)) (specIdealEquiv A (K.comap j))
    (affineOpenImageRingMap j).hom (affineOpenImageRingMap_center j K) ≫
      blowupAffineι K (affineOpenImage j)

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン開チャート上の blowup 比較射は基底上で可換。
方針：局所モデルの構造射、係数比較射、開像の係数写像の交換式を使う。
規約：KST §5、Stacks 080Y、基底は元の X。
使われ方：局所的な可逆中心による持ち上げの基底交換式。
-/
@[reassoc] theorem blowupAffineOpenMap_base :
    blowupAffineOpenMap j K ≫ blowupπ K =
      affineBlowupπ (specIdealEquiv A (K.comap j)) ≫ j := by
  unfold blowupAffineOpenMap
  rw [Category.assoc, blowupAffineι_π]
  change _ ≫ (affineBlowupπ (K.ideal (affineOpenImage j)) ≫
    (affineOpenImage j).2.fromSpec) = _
  rw [← Category.assoc, affineBlowupCenterMap_base, Category.assoc]
  exact congrArg (affineBlowupπ (specIdealEquiv A (K.comap j)) ≫ ·)
    (affineOpenImageRingMap_spec_base j)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
