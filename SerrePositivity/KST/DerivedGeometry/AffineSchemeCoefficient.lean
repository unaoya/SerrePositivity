module

public import SerrePositivity.KST.DerivedGeometry.OpenImmersionTensorRegular
public import SerrePositivity.KST.DerivedGeometry.AffineBaseChangeQuasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# 任意のアフィンスキーム上の係数環層

概要：具体的な Spec に限らず、任意のアフィンスキームで係数環層の準連接性を示す。
方針：標準射 X → Spec Γ(X,⊤) と構造層加群の制限比較を使う。
規約：基礎環の作用を大域切断への環準同型として指定する。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：大域切断の基礎環作用を標準アフィン模型へ送り引き戻すと元に戻る。
方針：toSpecΓ の大域切断写像と ΓSpecIso の逆の合成を計算する。
規約：Γ(X,⊤) の A 代数構造は a から作る。
使われ方：KST D4、Toën §3.2 のアフィン同型による輸送。
-/
lemma pullbackBaseMap_toSpecΓ :
    letI : Algebra A Γ(X, ⊤) := a.toAlgebra
    pullbackBaseMap (affineBaseMap A Γ(X, ⊤)) X.toSpecΓ = a := by
  let : Algebra A Γ(X, ⊤) := a.toAlgebra
  unfold pullbackBaseMap affineBaseMap
  rw [Scheme.toSpecΓ_appTop]
  change ((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom).hom.comp a = a
  rw [Iso.inv_hom_id]
  rfl

variable (H : Type u) [Ring H] [Algebra A H]

/--
概要：任意のアフィンスキーム上の具体的係数環層の正則 O 加群は準連接。
方針：Spec Γ(X,⊤) 上の既知の準連接性を標準同型に沿って制限する。
規約：H の平坦性・可換性は不要。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/
theorem affineSchemeCoefficientRegular_isQuasicoherent [IsAffine X] :
    (tensorCoefficientSheaf H a).regular.IsQuasicoherent := by
  let : Algebra A Γ(X, ⊤) := a.toAlgebra
  have h := tensorRegular_isQuasicoherent_pullback H (affineBaseMap A Γ(X, ⊤)) X.toSpecΓ
  rw [pullbackBaseMap_toSpecΓ a] at h
  exact h

end SerrePositivity.KST.DerivedGeometry
