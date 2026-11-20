module

public import Mathlib.AlgebraicGeometry.Limits

/-!
概要：KST §5 の局所商モデルの比較に使うファイバー積の同型。
方針：片方の対象の基底上の同型をファイバー積へ移す。
規約：スキーム圏の実際の射影を保存する同型として述べる。
使われ方：中心の局所商モデルと例外因子の局所商モデル。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

/--
概要：基底上の同型でファイバー積の第二の対象を置き換える同型。
方針：三つの対象の同型が誘導するファイバー積の写像を用いる。
規約：KST §5、第一射影は保存される。
使われ方：中心の閉部分スキームをアフィン商の Spec に置き換える。
-/
def pullbackRightIso {A B C D : Scheme.{u}} (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ B)
    (e : C ≅ D) (he : e.inv ≫ g = h) : pullback f g ≅ pullback f h :=
  asIso (pullback.map f g f h (𝟙 _) e.hom (𝟙 _) (by simp) (by
    rw [Category.comp_id, ← he, e.hom_inv_id_assoc]))

set_option backward.isDefEq.respectTransparency false in
/--
概要：第二の対象を基底上で同型に置き換えたとき、逆比較は第一射影を保存する。
方針：同型の順射を消去し、ファイバー積の写像の第一射影の公式を使う。
規約：KST §5、逆方向と元の第一射影を合成する。
使われ方：商の Spec への比較で包含射を計算する。
-/
@[reassoc] theorem pullbackRightIso_inv_fst {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ B) (e : C ≅ D) (he : e.inv ≫ g = h) :
    (pullbackRightIso f g h e he).inv ≫ pullback.fst f g = pullback.fst f h := by
  apply (cancel_epi (pullbackRightIso f g h e he).hom).mp
  rw [Iso.hom_inv_id_assoc]
  dsimp only [pullbackRightIso, asIso_hom, pullback.map]
  simp

/--
概要：二つの構造射の等式によるファイバー積の逆比較は第一射影を保存する。
方針：構造射の等式で移送して恒等的なファイバー積の写像へ帰着する。
規約：KST §5、対象そのものは固定する。
使われ方：例外因子の局所商同型の包含射の計算。
-/
@[reassoc] theorem pullbackCongrHom_inv_fst {A B C : Scheme.{u}}
    {f₁ f₂ : A ⟶ C} {g₁ g₂ : B ⟶ C} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.fst f₁ g₁ = pullback.fst f₂ g₂ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
