module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：テンソル積からの内部 Hom と反復内部 Hom の自然な同型。
方針：結合子で左随伴を比較し、右随伴の一意性を使う。
規約：通常の閉モノイダル圏の厳密な同型。
使われ方：Goerss–Jardine I §7、HA §1.4.2。円の smash の写像空間と二重 loop の比較。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomTensor
end SerrePositivity.KST.Spectra.InternalHomTensor
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor
open _root_.SerrePositivity.KST.Spectra.InternalHomTensor

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 概要：テンソル積の左積関手は反復内部 Hom を右随伴に持つ。
方針：二つの閉構造の随伴を合成し、結合子で左側を移す。
規約：右側の順序は A の内部 Hom の後で B の内部 Hom。
使われ方：HA §1.4.2。反復 curry の同型の実構成。 -/
def tensorAdjunction (A B : C) : tensorLeft (A ⊗ B) ⊣ ihom A ⋙ ihom B :=
  ((ihom.adjunction B).comp (ihom.adjunction A)).ofNatIsoLeft (tensorLeftTensor A B).symm

/-- 概要：テンソル積からの内部 Hom と反復内部 Hom の自然同型。
方針：同じ左随伴に対する右随伴の一意性を使う。
規約：A と B の対象に追加条件は不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。二つの円の smash からの写像の curry。 -/
def natIso (A B : C) : ihom (A ⊗ B) ≅ ihom A ⋙ ihom B :=
  (ihom.adjunction (A ⊗ B)).rightAdjointUniq (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction A B)

/-- 概要：標的を固定した反復 curry の同型。
方針：自然同型の成分を取る。
規約：B が外側、A が内側の内部 Hom。
使われ方：HA §1.4.2。二重 loop の単体集合の比較。 -/
def iso (A B Y : C) : (ihom (A ⊗ B)).obj Y ≅ (ihom B).obj ((ihom A).obj Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natIso A B).app Y

/-- 概要：反復 curry の同型の順写像は評価射を二度 curry したもの。
方針：右随伴の一意性の homEquiv の式を、合成随伴と結合子で展開する。
規約：結合子の逆で A と B の評価の括弧を合わせる。
使われ方：HA §1.4.2。源の変数の交換と同型の整合性。 -/
theorem hom_eq (A B Y : C) : (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Y).hom =
    curry (curry ((α_ A B ((ihom (A ⊗ B)).obj Y)).inv ≫
      (ihom.ev (A ⊗ B)).app Y)) := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (ihom.adjunction (A ⊗ B)) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction A B) Y
  have h' := congrArg ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction A B).homEquiv _ Y) h
  simp only [Equiv.apply_symm_apply] at h'
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv] at h'
  exact h'

/-- 概要：右随伴の一意性による同型は Mathlib の二重 curry の同型と一致。
方針：順写像の明示式を比較する。
規約：逆写像の等式は同型の外延性から従う。
使われ方：HA §1.4.2。既存の内部 Hom の交換同型との接続。 -/
theorem iso_eq_ihomCurryIso (A B Y : C) : _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Y = ihomCurryIso A B Y := by
  apply Iso.ext
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.hom_eq]
  rfl

/-- 概要：反復 curry の同型は標的の写像について自然。
方針：自然同型の自然性を取り出す。
規約：内部 Hom の後合成を二重に適用する。
使われ方：Goerss–Jardine I §7。標的の loop の符号反転の移送。 -/
@[reassoc]
theorem natural_post (A B : C) {Y Z : C} (f : Y ⟶ Z) :
    (ihom (A ⊗ B)).map f ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Y).hom ≫ (ihom B).map ((ihom A).map f) :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natIso A B).hom.naturality f

/-- 概要：テンソルの変数交換は反復内部 Hom の交換と一致する。
方針：Mathlib の curry 同型との一致を使い、交換同型の定義で中間の逆同型を打ち消す。
規約：源の braiding の前合成に対応する。
使われ方：Goerss–Jardine I §7、HA §1.4.2。二つの円の smash の交換を反復 loop へ移す。 -/
@[reassoc]
theorem natural_swap [BraidedCategory C] (A B Y : C) :
    (MonoidalClosed.pre (β_ A B).hom).app Y ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso B A Y).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A B Y).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  rfl

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.hom_eq := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.hom_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.iso := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.iso_eq_ihomCurryIso := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.natIso := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.natural_post := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.natural_post_assoc := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.natural_swap := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.natural_swap_assoc := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.tensorAdjunction := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.tensorAdjunction.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.tensorAdjunction.eq_1
