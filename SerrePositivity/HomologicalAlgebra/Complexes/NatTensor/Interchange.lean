module

public import SerrePositivity.HomologicalAlgebra.Complexes.NatTensor.Symmetry

/-!
# 自然数鎖テンソルの四因子交換

概要：Berger–Fresse §1.1.4 の中間二因子の交換を実際の鎖同型として構成する。
方針：既存の結合子と符号付き交換を合成する。
規約：大域的な対称モノイダル instance は追加しない。
使われ方：shuffle と AW の余代数適合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NatTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：自然数鎖の全テンソル（BF §1.1.4）。
方針：Mathlib の全複体を使う。
規約：既存の Koszul 微分を保持する。
使われ方：四重テンソルの記法を揃える。 -/
abbrev tensor (K L : ChainComplex (ModuleCat.{u} A) ℕ) := HomologicalComplex.tensorObj K L

/-- 概要：結合子の順方向の斉次包含公式（BF §1.1.4）。
方針：三つの次数の直和包含を結合子の標準公式へ代入する。
規約：三つの次数の和は n。
使われ方：四因子交換の第一・第四段階。 -/
@[reassoc]
lemma inclusion_associator_hom
    (P Q T : ChainComplex (ModuleCat.{u} A) ℕ) (i j k n : ℕ) (h : i + j + k = n) :
    (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) T (i + j) k n h ≫
      (HomologicalComplex.associator P Q T).hom.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).hom ≫
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
      ιTensorObj P (_root_.SerrePositivity.NatTensor.tensor Q T) i (j + k) n (by omega) :=
  GradedObject.Monoidal.ιTensorObj₃'_associator_hom P.X Q.X T.X i j k n h

/-- 概要：結合子の逆方向の斉次包含公式（BF §1.1.4）。
方針：逆結合子の標準の直和包含公式を使う。
規約：同じ三つの次数を左結合へ移す。
使われ方：四因子交換の第二・第五段階。 -/
@[reassoc]
lemma inclusion_associator_inv
    (P Q T : ChainComplex (ModuleCat.{u} A) ℕ) (i j k n : ℕ) (h : i + j + k = n) :
    (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
      ιTensorObj P (_root_.SerrePositivity.NatTensor.tensor Q T) i (j + k) n (by omega) ≫
      (HomologicalComplex.associator P Q T).inv.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).inv ≫
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) T (i + j) k n h :=
  GradedObject.Monoidal.ιTensorObj₃_associator_inv P.X Q.X T.X i j k n h

/-- 概要：二つの鎖同型の全テンソル（BF §1.1.4）。
方針：二変数関手の同型を全複体へ送る。
規約：二因子とも実際の鎖同型。
使われ方：四因子交換の左右の固定因子。 -/
def tensorIso {P P' Q Q' : ChainComplex (ModuleCat.{u} A) ℕ}
    (e : P ≅ P') (f : Q ≅ Q') : _root_.SerrePositivity.NatTensor.tensor P Q ≅ _root_.SerrePositivity.NatTensor.tensor P' Q' :=
  HomologicalComplex₂.total.mapIso
    (Iso.app ((curriedTensor (ModuleCat A)).mapBifunctorHomologicalComplex
      (.down ℕ) (.down ℕ) |>.mapIso e) Q ≪≫
      (((curriedTensor (ModuleCat A)).mapBifunctorHomologicalComplex
        (.down ℕ) (.down ℕ)).obj P').mapIso f) (.down ℕ)

/-- 概要：四重テンソルの中間二因子を交換する鎖同型（BF §1.1.4）。
方針：結合子と符号付き交換を五段階で合成する。
規約：元の四因子の第一・第四因子は保つ。
使われ方：AW 余代数のテンソルの余積。 -/
def interchange (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ) :
    _root_.SerrePositivity.NatTensor.tensor (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U) ≅
      _root_.SerrePositivity.NatTensor.tensor (_root_.SerrePositivity.NatTensor.tensor P T) (_root_.SerrePositivity.NatTensor.tensor Q U) :=
  HomologicalComplex.associator P Q (_root_.SerrePositivity.NatTensor.tensor T U) ≪≫
    _root_.SerrePositivity.NatTensor.tensorIso (Iso.refl P) (HomologicalComplex.associator Q T U).symm ≪≫
    _root_.SerrePositivity.NatTensor.tensorIso (Iso.refl P)
      (_root_.SerrePositivity.NatTensor.tensorIso (_root_.SerrePositivity.NatTensor.symmetry Q T) (Iso.refl U)) ≪≫
    _root_.SerrePositivity.NatTensor.tensorIso (Iso.refl P) (HomologicalComplex.associator T Q U) ≪≫
    (HomologicalComplex.associator P T (_root_.SerrePositivity.NatTensor.tensor Q U)).symm

end SerrePositivity.NatTensor
