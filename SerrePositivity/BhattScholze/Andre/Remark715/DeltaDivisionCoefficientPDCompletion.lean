module

public import SerrePositivity.BhattScholze.Andre.Remark715.PDCompletionCoordinateEquiv
public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionCoefficientAut

/-!
# André E1・E2：raw 係数 δ 比較の実導来完備化への延長

## 概要

係数 δ 自己同型による raw 除算包の比較は、同じ標準係数射を保って
実導来 (p,d) 完備化の H⁰ の δ 環同型へ延長する。
BS Rem 7.15（著者版 p.62）の Frobenius 比較の完備化段階。

## 方針

raw 比較が分母の係数像を対応する係数像へ送る公式を、座標付き実完備化の比較へ渡す。

## 規約

源の raw 包の実 H⁰ を用い、δ 完全化や perfectoid 商は取らない。

## 使われ方

係数 Frobenius と指数成分、全体 Frobenius の raw 比較を実完備化へ持ち上げる。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (e : A ≃+* A) (he : D.IsDeltaHom D e.toRingHom)
variable (d : A) (a : σ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "DL" => deltaAdjoinDivisionStructure D d a
local notation "DM" => deltaAdjoinDivisionStructure D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "F" => deltaDivisionCoefficientAutEquiv D e he d a

/-- 概要：係数自己同型による raw 比較は実完備化 H⁰ の環同型へ延長する。
方針：分母の係数像を保つ raw 環同型を座標付き完備化の一般比較へ渡す。
規約：両側の完備化の座標を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 比較の実完備化。 -/
def deltaDivisionCoefficientPDCompletionEquiv :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    PDCompletionH0 L p (jL d) ≃+* PDCompletionH0 M p (jM (e d)) :=
  pdCompletionCoordinateEquiv p F (jL d) (jM (e d))
    (deltaDivisionCoefficientAutEquiv_coeff D e he d a d)

/-- 概要：実完備化同型は raw の全ての元の標準像を対応させる。
方針：座標付き完備化比較の単位公式を使う。
規約：raw 比較そのものを同じ元の像に適用する。
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の剰余比較の係数。 -/
theorem deltaDivisionCoefficientPDCompletionEquiv_unit (t : L) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    deltaDivisionCoefficientPDCompletionEquiv D e he d a (pdCompletionUnit L p (jL d) t) =
      pdCompletionUnit M p (jM (e d)) (F t) :=
  pdCompletionCoordinateEquiv_unit p F (jL d) (jM (e d))
    (deltaDivisionCoefficientAutEquiv_coeff D e he d a d) t

/-- 概要：実完備化同型は元の係数 b を e(b) の標準完備化像へ送る。
方針：raw 単位の公式と raw 比較の係数公式を合成する。
規約：同じ標準係数射を使い続ける。
使われ方：BS Rem 7.15（著者版 p.62）の係数半線形性の記録。 -/
theorem deltaDivisionCoefficientPDCompletionEquiv_coeff (b : A) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    deltaDivisionCoefficientPDCompletionEquiv D e he d a
      (pdCompletionUnit L p (jL d) (jL b)) = pdCompletionUnit M p (jM (e d)) (jM (e b)) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  rw [deltaDivisionCoefficientPDCompletionEquiv_unit, deltaDivisionCoefficientAutEquiv_coeff]

/-- 概要：raw 係数比較の実完備化同型は既存の完備化 δ 構造を保つ。
方針：raw 比較の δ 互換性を座標付き完備化比較の δ 互換性へ渡す。
規約：係数の正則性は追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の実 δ 完備化後の比較。 -/
theorem deltaDivisionCoefficientPDCompletionEquiv_isDeltaHom :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    (deltaPDCompletionStructure DL (jL d)).IsDeltaHom
      (deltaPDCompletionStructure DM (jM (e d)))
      (deltaDivisionCoefficientPDCompletionEquiv D e he d a).toRingHom :=
  pdCompletionCoordinateEquiv_isDeltaHom p DL DM F
    (deltaDivisionCoefficientAutEquiv_isDeltaHom D e he d a) (jL d) (jM (e d))
    (deltaDivisionCoefficientAutEquiv_coeff D e he d a d)

end SerrePositivity.BhattScholze.Andre
