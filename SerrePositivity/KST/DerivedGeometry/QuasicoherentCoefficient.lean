module

public import SerrePositivity.KST.DerivedGeometry.CoefficientForget

/-!
# 準連接な係数加群層の圏

概要：係数加群層のうち、構造層上で準連接なものの充満部分圏を定義する。
方針：実際の係数忘却と Mathlib の準連接性を使う。
規約：複体の各項と導来コホモロジーの条件を区別する。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン比較。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：係数加群層を構造層上へ忘れたときの準連接性という対象条件。
方針：実際の忘却関手の像に Mathlib の条件を適用する。
規約：層レベルの条件であり導来圏の条件ではない。
使われ方：KST D4、Toën §3.2 のアフィン加群との比較。
-/
def hasQuasicoherentUnderlying : ObjectProperty B.Modules :=
  fun M => (B.forget.obj M).IsQuasicoherent

/--
概要：準連接な基礎構造層加群を持つ条件は同型で不変。
方針：忘却した同型で準連接性を移す。
規約：係数環層自体の準連接性はこの定義には不要。
使われ方：KST D4、Toën §3.2 の準連接係数加群の部分圏。
-/
instance hasQuasicoherentUnderlying_closedUnderIso :
    B.hasQuasicoherentUnderlying.IsClosedUnderIsomorphisms where
  of_iso e h := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (B.forget.mapIso e) h

/--
概要：準連接な基礎 O 加群を持つ係数加群層の圏。
方針：係数加群層の実際の充満部分圏を取る。
規約：D_qc と同一視しない。
使われ方：KST D4・T1′、Toën §3.2 の層レベルのアフィン比較。
-/
abbrev QCoh := B.hasQuasicoherentUnderlying.FullSubcategory

/--
概要：準連接係数加群層から係数加群層全体への包含。
方針：対象条件の充満部分圏の標準包含を使う。
規約：射は係数加群層の射を保つ。
使われ方：KST D4、Toën §3.2 の大域切断関手の定義。
-/
def qcohInclusion : B.QCoh ⥤ B.Modules := ObjectProperty.ι _

/--
概要：準連接係数加群層を準連接 O 加群層へ忘れる。
方針：係数忘却を対象条件の部分圏へ持ち上げる。
規約：構造層上の準連接性は入力の対象条件から得る。
使われ方：KST D4・T1′、Toën §3.2 の通常の tilde 同値への接続。
-/
def qcohForget : B.QCoh ⥤
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (B.qcohInclusion ⋙ B.forget) fun M => M.property

/--
概要：準連接係数加群層から準連接 O 加群層への忘却は忠実。
方針：元の係数忘却の忠実性を充満部分圏へ制限する。
規約：大域切断の忠実性は別にアフィンの場合に証明する。
使われ方：KST D4、Toën §3.2 のアフィン比較。
-/
instance qcohForget_faithful : B.qcohForget.Faithful where
  map_injective {M N} f g h := by
    apply ObjectProperty.hom_ext
    apply B.forget.map_injective
    exact congrArg (fun q => q.hom) h

/--
概要：準連接係数加群層の忘却は同型を反映する。
方針：係数忘却と充満部分圏の包含が同型を反映することを使う。
規約：準連接性以外の有限性を要求しない。
使われ方：KST D4、Toën §3.2 の大域切断の保存性への接続。
-/
instance qcohForget_reflectsIsomorphisms : B.qcohForget.ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have : IsIso (B.forget.map f.hom) :=
      Functor.map_isIso (ObjectProperty.ι _) (B.qcohForget.map f)
    have : IsIso f.hom := isIso_of_reflects_iso f.hom B.forget
    have : IsIso ((ObjectProperty.ι B.hasQuasicoherentUnderlying).map f) := ‹IsIso f.hom›
    exact isIso_of_reflects_iso f (ObjectProperty.ι B.hasQuasicoherentUnderlying)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
