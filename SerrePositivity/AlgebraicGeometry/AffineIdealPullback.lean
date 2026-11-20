module

public import SerrePositivity.AlgebraicGeometry.SpecIdeal
public import SerrePositivity.AlgebraicGeometry.SubschemeAffinePullback

/-!
概要：KST §5、Stacks 080Y の任意のアフィン局所射による中心イデアルの逆像。
方針：閉部分スキームの逆像の商 Spec モデルと Spec の核イデアルの計算を使う。
規約：基底全体や局所射の平坦性は仮定しない。
使われ方：局所的な中心の可逆性と blowup の普遍写像を接続する。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：Spec の射の核イデアル層は元の環準同型の核に対応する。
方針：核の全切断公式と ΓSpec 同型の自然性・単射性を使う。
規約：KST §5、Stacks 080Y、任意の環準同型。
使われ方：商 Spec への同定から逆像中心の環イデアルを読み取る。
-/
theorem specIdealEquiv_ker_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    specIdealEquiv A (Spec.map φ).ker = RingHom.ker φ.hom := by
  rw [specIdealEquiv_apply, (Spec.map φ).ker_apply ⟨⊤, isAffineOpen_top (Spec A)⟩]
  ext r
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv r) = 0 ↔ φ r = 0
  have heq : (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv r) =
      (Scheme.ΓSpecIso B).inv (φ r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [heq]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心を標準アフィン Spec へ引き戻すと、その切断イデアルに対応する。
方針：実際の逆像を切断イデアルの商の Spec と同定し、核イデアルを計算する。
規約：KST §5、Stacks 080Y、中心のスキーム構造を保持する。
使われ方：任意のアフィン局所係数写像による中心の逆像。
-/
theorem specIdealEquiv_comap_fromSpec {X : Scheme.{u}} (K : X.IdealSheafData)
    (U : X.affineOpens) :
    specIdealEquiv Γ(X, U.1) (K.comap U.2.fromSpec) = K.ideal U := by
  have hker : K.comap U.2.fromSpec =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K.ideal U)))).ker := by
    unfold Scheme.IdealSheafData.comap
    rw [← Scheme.Hom.ker_comp_of_isIso (subschemeSpecPullbackIso K U).inv,
      subschemeSpecPullbackIso_inv_fst]
  rw [hker, specIdealEquiv_ker_specMap]
  exact Ideal.mk_ker

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン開集合の Spec を経由する任意の局所射による中心の逆像は拡大イデアル。
方針：逆像の合成則と Spec のイデアル対応の逆像公式を使う。
規約：KST §5、Stacks 080Y、係数環準同型は任意。
使われ方：構成した局所的な射で中心が正則単項となることの判定。
-/
theorem specIdealEquiv_comap_affine_local {X : Scheme.{u}} (K : X.IdealSheafData)
    (U : X.affineOpens) (A : CommRingCat.{u}) (φ : Γ(X, U.1) ⟶ A) :
    specIdealEquiv A (K.comap (Spec.map φ ≫ U.2.fromSpec)) = (K.ideal U).map φ.hom := by
  rw [Scheme.IdealSheafData.comap_comp, specIdealEquiv_comap, specIdealEquiv_comap_fromSpec]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
