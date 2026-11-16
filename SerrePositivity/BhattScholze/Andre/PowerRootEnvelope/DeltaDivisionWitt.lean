module

public import SerrePositivity.BhattScholze.Delta.Division.Family
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import SerrePositivity.BhattScholze.Andre.Envelope.PDivision
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion

/-!
# raw δ 除算包の係数比較と Witt 普遍性

## 概要
係数 δ 自己同型による raw 包の比較と導来完備化への延長、有限 δ 関係商の mod p と最高変数、Witt 解からの環射と二元剰余の Witt 普遍性、distinguished 分母の正規化と自然性、Frobenius 分母の剰余と p 除算剰余、raw 包の完備化の普遍性とねじれ除去後との比較、raw p 除算包の係数商と主 pd 表示。
BS 著者版 Remark 7.15 のモニック根の包に使う、δ 除算包の係数比較と Witt 座標での普遍性を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPrism`、`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/PowerRootPolynomial`、`Variants/Auxiliary`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## 係数 δ 自己同型による raw 除算包の比較

## 概要

係数環の δ 自己同型 e は、raw δ 除算包 A{a/d} と A{e(a)/e(d)} の環同型を誘導する。
BS 著者版 Remark 7.15（著者版 p.62）、BS 著者版 Corollary 2.39（p.25）の Frobenius による係数変更への準備。

## 方針

除算解を同じ添字の初期変数へ送り、普遍性で順射と逆射を作る。
逆合成は係数と初期除算変数上の外延性で確認する。

## 規約

完備化・ねじれ除去・pd 包との同定は含めない。係数自己同型の向きを明示する。

## 使われ方

完全な無限根 δ 入力環の Frobenius 同型を代入して raw 包の係数変更を具体化する。
-/

@[expose] public noncomputable section DeltaDivisionCoefficientAut

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (e : A ≃+* A) (he : D.IsDeltaHom D e.toRingHom)
variable (d : A) (a : σ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "DL" => deltaAdjoinDivisionStructure D d a
local notation "DM" => deltaAdjoinDivisionStructure D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "vL" => deltaAdjoinDivisionVariable D d a
local notation "vM" => deltaAdjoinDivisionVariable D (e d) (fun s => e (a s))

/-- 概要：係数自己同型と同じ除算変数を延長する順射。
方針：δ 除算の普遍性に標準関係式を供給する。
規約：分母も入力族も e で送る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw Frobenius 係数変更。 -/
def deltaDivisionCoefficientAutMap : L →+* M :=
  (existsUnique_deltaAdjoinDivisionHom D DM d a ((jM).comp e.toRingHom)
    ((deltaAdjoinDivisionMap_isDeltaHom D (e d) (fun s => e (a s))).comp he) vM
    (fun s => deltaAdjoinDivision_relation D (e d) (fun t => e (a t)) s)).choose

/-- 概要：順射は δ、係数射、全初期除算変数と両立する。
方針：普遍性の選択した射の仕様を使う。
規約：係数射の合成に e を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用と逆合成の照合。 -/
theorem deltaDivisionCoefficientAutMap_spec :
    (DL).IsDeltaHom DM (deltaDivisionCoefficientAutMap D e he d a) ∧
    (deltaDivisionCoefficientAutMap D e he d a).comp jL = (jM).comp e.toRingHom ∧
    ∀ s, deltaDivisionCoefficientAutMap D e he d a (vL s) = vM s :=
  (existsUnique_deltaAdjoinDivisionHom D DM d a ((jM).comp e.toRingHom)
    ((deltaAdjoinDivisionMap_isDeltaHom D (e d) (fun s => e (a s))).comp he) vM
    (fun s => deltaAdjoinDivision_relation D (e d) (fun t => e (a t)) s)).choose_spec.1

/-- 概要：逆係数自己同型と同じ除算変数を延長する逆射。
方針：元の標準関係式を e の逆合成で書き直して普遍性を使う。
規約：始域は e で送った関係族の包。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 係数変更の可逆性。 -/
def deltaDivisionCoefficientAutInverse : M →+* L :=
  (existsUnique_deltaAdjoinDivisionHom D DL (e d) (fun s => e (a s))
    ((jL).comp e.symm.toRingHom) ((deltaAdjoinDivisionMap_isDeltaHom D d a).comp he.symm)
    vL (fun s => by simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] using deltaAdjoinDivision_relation D d a s)).choose

/-- 概要：逆射は δ、逆係数射、全初期除算変数と両立する。
方針：逆射を選んだ普遍性の仕様を使う。
規約：係数には e⁻¹ を適用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の逆合成の計算。 -/
theorem deltaDivisionCoefficientAutInverse_spec :
    (DM).IsDeltaHom DL (deltaDivisionCoefficientAutInverse D e he d a) ∧
    (deltaDivisionCoefficientAutInverse D e he d a).comp jM = (jL).comp e.symm.toRingHom ∧
    ∀ s, deltaDivisionCoefficientAutInverse D e he d a (vM s) = vL s :=
  (existsUnique_deltaAdjoinDivisionHom D DL (e d) (fun s => e (a s))
    ((jL).comp e.symm.toRingHom) ((deltaAdjoinDivisionMap_isDeltaHom D d a).comp he.symm)
    vL (fun s => by simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] using deltaAdjoinDivision_relation D d a s)).choose_spec.1

/-- 概要：係数 δ 自己同型は raw δ 除算包の環同型を誘導する。
方針：順射と逆射の合成を係数・初期変数で検証する。
規約：d の正則性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw Frobenius 引戻し比較の代数的入力。 -/
def deltaDivisionCoefficientAutEquiv : L ≃+* M := by
  have hF := deltaDivisionCoefficientAutMap_spec D e he d a
  have hG := deltaDivisionCoefficientAutInverse_spec D e he d a
  apply RingEquiv.ofRingHom (deltaDivisionCoefficientAutMap D e he d a)
    (deltaDivisionCoefficientAutInverse D e he d a)
  · apply deltaAdjoinDivisionHom_ext D DM (e d) (fun s => e (a s))
      _ _ (hF.1.comp hG.1) (DM).isDeltaHom_id
    · rw [RingHom.comp_assoc, hG.2.1, ← RingHom.comp_assoc, hF.2.1]
      ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
        RingHom.id_apply]
    · intro s
      rw [RingHom.comp_apply, hG.2.2, hF.2.2]
      rfl
  · apply deltaAdjoinDivisionHom_ext D DL d a _ _ (hG.1.comp hF.1) (DL).isDeltaHom_id
    · rw [RingHom.comp_assoc, hF.2.1, ← RingHom.comp_assoc, hG.2.1]
      ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
        RingHom.id_apply]
    · intro s
      rw [RingHom.comp_apply, hF.2.2, hG.2.2]
      rfl

/-- 概要：raw 包の比較同型は元の係数を e で送る。
方針：順射の係数合成の等式を各元で評価する。
規約：同型は係数に関して e 半線形。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用の記録。 -/
theorem deltaDivisionCoefficientAutEquiv_coeff (b : A) :
    deltaDivisionCoefficientAutEquiv D e he d a (jL b) = jM (e b) :=
  DFunLike.congr_fun (deltaDivisionCoefficientAutMap_spec D e he d a).2.1 b

/-- 概要：raw 包の比較同型は全初期除算変数の添字を保つ。
方針：順射の標準変数公式を使う。
規約：δ 反復前の初期変数について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根方程式の比較。 -/
theorem deltaDivisionCoefficientAutEquiv_variable (s : σ) :
    deltaDivisionCoefficientAutEquiv D e he d a (vL s) = vM s :=
  (deltaDivisionCoefficientAutMap_spec D e he d a).2.2 s

/-- 概要：raw 包の比較同型は実 δ 射。
方針：順射の δ 互換性を使う。
規約：両側の既存の商 δ 構造を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 完備化に進む入力。 -/
theorem deltaDivisionCoefficientAutEquiv_isDeltaHom :
    (DL).IsDeltaHom DM (deltaDivisionCoefficientAutEquiv D e he d a).toRingHom :=
  (deltaDivisionCoefficientAutMap_spec D e he d a).1

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionCoefficientAut

/-! ## raw 係数 δ 比較の実導来完備化への延長

## 概要

係数 δ 自己同型による raw 除算包の比較は、同じ標準係数射を保って
実導来 (p,d) 完備化の H⁰ の δ 環同型へ延長する。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 比較の完備化段階。

## 方針

raw 比較が分母の係数像を対応する係数像へ送る公式を、座標付き実完備化の比較へ渡す。

## 規約

源の raw 包の実 H⁰ を用い、δ 完全化や perfectoid 商は取らない。

## 使われ方

係数 Frobenius と指数成分、全体 Frobenius の raw 比較を実完備化へ持ち上げる。
-/

@[expose] public noncomputable section DeltaDivisionCoefficientPDCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 比較の実完備化。 -/
def deltaDivisionCoefficientPDCompletionEquiv :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    PDCompletionH0 L p (jL d) ≃+* PDCompletionH0 M p (jM (e d)) :=
  pdCompletionCoordinateEquiv p F (jL d) (jM (e d))
    (deltaDivisionCoefficientAutEquiv_coeff D e he d a d)

/-- 概要：実完備化同型は raw の全ての元の標準像を対応させる。
方針：座標付き完備化比較の単位公式を使う。
規約：raw 比較そのものを同じ元の像に適用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余比較の係数。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数半線形性の記録。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 δ 完備化後の比較。 -/
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

end DeltaDivisionCoefficientPDCompletion

/-! ## 任意の Witt 解から raw δ 除算包への通常環射

## 概要

W(d)w_s=W(a_s) を満たす任意の Witt 点から A{a/d} への通常評価を作る。
BS 著者版 Remark 7.15（著者版 p.62）の分母正規化に使う。

## 方針

既存の逆 Witt 座標と jet 消滅比較を使って、全 δ 関係を殺す。

## 規約

源の p 正則性と ghost 射の単射性を明示し、終域の δ 構造は要求しない。
原典とは異なる通常環射による具体的比較である。

## 使われ方

Witt 解の単元倍による変数変換を raw 包の通常環射へ移す。
-/

@[expose] public noncomputable section DeltaDivisionWittEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B σ : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (q : A →+* B) (w : σ → WittVector p B)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => relativeFreeDeltaStructure σ D

/-- 概要：任意の Witt 点の全係数を自由 δ 環の逆 Witt 座標へ代入する。
方針：逆 Witt 座標の通常多項式評価を合成する。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
def deltaDivisionWittEval : L₀ →+* B :=
  (MvPolynomial.eval₂Hom q (fun z : σ × ℕ ↦
    (w z.1).coeff z.2)).comp
      (relativeFreeWittInverseMap D hpA).toRingHom

/-- 概要：Witt 点による通常評価は元の係数射を保つ。
方針：逆座標の係数公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_C (r : A) :
    deltaDivisionWittEval D hpA q w (MvPolynomial.C r) = q r := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (MvPolynomial.C r)) = _
  rw [show relativeFreeWittInverseMap D hpA (MvPolynomial.C r) = MvPolynomial.C r from
    AlgHom.commutes (relativeFreeWittInverseMap D hpA) r, MvPolynomial.eval₂Hom_C]

/-- 概要：自由変数の各 Witt 係数は指定した点の同じ係数へ送られる。
方針：逆座標の変数公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_coefficient (s : σ) (n : ℕ) :
    deltaDivisionWittEval D hpA q w (relativeFreeWittGhostCoefficient D s n) =
      (w s).coeff n := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (relativeFreeWittGhostCoefficient D s n)) = _
  rw [relativeFreeWittInverseMap_coefficient, MvPolynomial.eval₂Hom_X']

/-- 概要：自由初期変数の全 Witt 元は指定した点へ送られる。
方針：各係数で評価の公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_witt_X (s : σ) :
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) =
        w s := by
  ext n
  rw [WittVector.map_coeff]
  exact deltaDivisionWittEval_coefficient D hpA q w s n

/-- 概要：基底の全 Witt 元は元の通常係数射で送られる。
方針：自由 δ 構造の係数自然性を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_witt_C
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀)) (r : A) :
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C r)) =
        WittVector.map q (deltaWittGhostVector D r) := by
  ext n
  rw [WittVector.map_coeff, deltaWittGhostVector_relativeFree_C_coeff D hgL,
    deltaDivisionWittEval_C, WittVector.map_coeff]

/-- 概要：Witt 除算方程式を満たす点は初期関係の全 Witt 元を殺す。
方針：Witt 環射の乗法性と指定した方程式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_kills_witt_relation (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (s : σ) :
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C d * MvPolynomial.X (s, 0) -
        MvPolynomial.C (a s))) = 0 := by
  change WittVector.map (deltaDivisionWittEval D hpA q w)
    (deltaWittGhostRingHom F₀ hgL (MvPolynomial.C d * MvPolynomial.X (s, 0) -
      MvPolynomial.C (a s))) = 0
  rw [map_sub, map_mul, map_sub, map_mul]
  change WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C d)) *
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) -
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C (a s))) = 0
  rw [deltaDivisionWittEval_witt_C D hpA q w hgL,
    deltaDivisionWittEval_witt_X, deltaDivisionWittEval_witt_C D hpA q w hgL]
  exact sub_eq_zero.mpr (hw s)

/-- 概要：Witt 解の通常評価は実除算関係の全 δ 反復を殺す。
方針：Witt 係数の消滅を既存の jet 比較で移す。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_kills_iterated_relation (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (s : σ) (n : ℕ) :
    deltaDivisionWittEval D hpA q w
      (deltaDivisionIteratedRelation D d a s n) = 0 := by
  have hpL : Function.Injective (fun x : L₀ ↦ (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hw := deltaDivisionWittEval_kills_witt_relation D hpA q w d a hgL hw s
  have hc : ∀ i ≤ n, deltaDivisionWittEval D hpA q w
      ((deltaWittGhostVector F₀ (MvPolynomial.C d * MvPolynomial.X (s, 0) -
        MvPolynomial.C (a s))).coeff i) = 0 := by
    intro i _
    have h := congrArg (fun w : WittVector p B ↦ w.coeff i) hw
    simpa only [WittVector.map_coeff, WittVector.zero_coeff] using h
  have hj := (deltaWittGhostVector_jets_zero_iff F₀ hpL hgL
    (deltaDivisionWittEval D hpA q w)
    (MvPolynomial.C d * MvPolynomial.X (s, 0) -
      MvPolynomial.C (a s)) n).mpr hc
  exact hj n le_rfl

/-- 概要：任意の Witt 解から raw δ 除算包への通常環射を構成する。
方針：全 δ 反復関係を殺す通常評価を商へ降ろす。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
def deltaDivisionWittMap (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) : DeltaAdjoinDivision D d a →+* B :=
  deltaDivisionIteratedRelationsLift D d a (deltaDivisionWittEval D hpA q w)
    (deltaDivisionWittEval_kills_iterated_relation D hpA q w d a hgL hw)

/-- 概要：構成した射は自由環上の指定した評価を延長する。
方針：商射の定義を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittMap_comp_mk (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) :
    (deltaDivisionWittMap D hpA q w d a hgL hw).comp
      (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = deltaDivisionWittEval D hpA q w := rfl

/-- 概要：構成した raw 包の射は元の係数射を保つ。
方針：自由環上の係数公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittMap_coeff (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (r : A) :
    deltaDivisionWittMap D hpA q w d a hgL hw
      (deltaAdjoinDivisionMap D d a r) = q r :=
  deltaDivisionWittEval_C D hpA q w r


/-- 概要：raw 包の各自由変数の全 Witt 座標を通常商射で送った点。
方針：自由 δ 環上の Witt 元をそのまま raw 商へ送る。
規約：raw 包の δ 構造や終域の正則性を使わない定義。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常比較射の生成元。 -/
def deltaDivisionRawWittPoint (d : A) (a : σ → A) (s : σ) :
    WittVector p (DeltaAdjoinDivision D d a) :=
  WittVector.map (Ideal.Quotient.mk _)
    (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0)))

/-- 概要：Witt 解から作った通常射は raw Witt 点を指定した解へ送る。
方針：各係数で自由環の評価公式を使う。
規約：全ての添字 s の全 Witt 係数を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の単元変換で作る射の逆合成。 -/
theorem deltaDivisionWittMap_point (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (s : σ) :
    WittVector.map (deltaDivisionWittMap D hpA q w d a hgL hw)
      (deltaDivisionRawWittPoint D d a s) = w s := by
  ext n
  change deltaDivisionWittEval D hpA q w (relativeFreeWittGhostCoefficient D s n) = _
  exact deltaDivisionWittEval_coefficient D hpA q w s n

include hpA in
/-- 概要：raw 包の通常環射は元の係数と全 raw Witt 点で決まる。
方針：商射の全射性と可逆な Witt 座標変換で多項式の外延性へ帰着する。
規約：比較する射には δ 互換性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較の両逆合成。 -/
theorem deltaDivisionRingHom_ext_of_wittPoint (d : A) (a : σ → A)
    (f g : DeltaAdjoinDivision D d a →+* B)
    (hc : ∀ r, f (deltaAdjoinDivisionMap D d a r) =
      g (deltaAdjoinDivisionMap D d a r))
    (hw : ∀ s, WittVector.map f (deltaDivisionRawWittPoint D d a s) =
      WittVector.map g (deltaDivisionRawWittPoint D d a s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  have he : (f.comp (Ideal.Quotient.mk _)).comp
        (relativeFreeWittCoordinateEquiv D hpA).toRingHom =
      (g.comp (Ideal.Quotient.mk _)).comp
        (relativeFreeWittCoordinateEquiv D hpA).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA
          (MvPolynomial.C r))) =
        g (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA (MvPolynomial.C r)))
      rw [show relativeFreeWittCoordinateEquiv D hpA (MvPolynomial.C r) =
        MvPolynomial.C r from AlgEquiv.commutes (relativeFreeWittCoordinateEquiv D hpA) r]
      exact hc r
    · intro sn
      obtain ⟨s, n⟩ := sn
      change f (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA
          (MvPolynomial.X (s, n)))) =
        g (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA (MvPolynomial.X (s, n))))
      rw [relativeFreeWittCoordinateEquiv_X]
      have h := congrArg (fun z : WittVector p B => z.coeff n) (hw s)
      simpa only [deltaDivisionRawWittPoint, WittVector.map_coeff,
        relativeFreeWittGhostCoefficient] using h
  apply RingHom.ext
  intro r
  obtain ⟨t, rfl⟩ := (relativeFreeWittCoordinateEquiv D hpA).surjective r
  exact RingHom.congr_fun he t

include hpA in
/-- 概要：raw Witt 点は元の全 Witt 除算方程式を満たす。
方針：通常商での全 δ 反復関係の消滅を Witt 係数の消滅へ戻す。
規約：raw 包の p 正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 包同士の変数変換の入力。 -/
theorem deltaDivisionRawWittPoint_relation (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀)) (s : σ) :
    WittVector.map (deltaAdjoinDivisionMap D d a) (deltaWittGhostVector D d) *
        deltaDivisionRawWittPoint D d a s =
      WittVector.map (deltaAdjoinDivisionMap D d a) (deltaWittGhostVector D (a s)) := by
  let j : L₀ →+* DeltaAdjoinDivision D d a := Ideal.Quotient.mk _
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hC (r : A) :
      WittVector.map j (deltaWittGhostVector F₀ (MvPolynomial.C r)) =
        WittVector.map (deltaAdjoinDivisionMap D d a) (deltaWittGhostVector D r) := by
    ext n
    rw [WittVector.map_coeff, deltaWittGhostVector_relativeFree_C_coeff D hgL,
      WittVector.map_coeff]
    rfl
  have hz : WittVector.map j (deltaWittGhostVector F₀
      (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))) = 0 := by
    ext n
    rw [WittVector.map_coeff, WittVector.zero_coeff]
    apply (deltaWittGhostVector_jets_zero_iff F₀ hpL hgL j
      (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) n).mp
      (fun i _ => deltaDivisionIteratedRelation_quotient_eq_zero D d a s i) n le_rfl
  change WittVector.map j (deltaWittGhostRingHom F₀ hgL
    (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))) = 0 at hz
  rw [map_sub, map_mul, map_sub, map_mul] at hz
  change WittVector.map j (deltaWittGhostVector F₀ (MvPolynomial.C d)) *
    deltaDivisionRawWittPoint D d a s -
      WittVector.map j (deltaWittGhostVector F₀ (MvPolynomial.C (a s))) = 0 at hz
  rw [hC, hC] at hz
  exact sub_eq_zero.mp hz

include hpA in
/-- 概要：係数射と全 Witt 解を指定すると raw 包からの通常環射が一意に存在する。
方針：Witt 解による通常評価で存在を、Witt 点の外延性で一意性を示す。
規約：終域の δ 構造・p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余比較に使う具体的普遍性。 -/
theorem existsUnique_deltaDivisionWittMap (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) :
    ∃! h : DeltaAdjoinDivision D d a →+* B,
      (∀ r, h (deltaAdjoinDivisionMap D d a r) = q r) ∧
        ∀ s, WittVector.map h (deltaDivisionRawWittPoint D d a s) = w s := by
  refine ⟨deltaDivisionWittMap D hpA q w d a hgL hw, ⟨?_, ?_⟩, ?_⟩
  · exact deltaDivisionWittMap_coeff D hpA q w d a hgL hw
  · exact deltaDivisionWittMap_point D hpA q w d a hgL hw
  · intro h hh
    apply deltaDivisionRingHom_ext_of_wittPoint D hpA d a
    · intro r
      rw [hh.1, deltaDivisionWittMap_coeff]
    · intro s
      rw [hh.2, deltaDivisionWittMap_point]

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionWittEvaluation

/-! ## raw 二元剰余の Witt 普遍性

## 概要

A{b/c}/(p,d) の係数射と Witt 点、その通常環射への普遍性を明示する。
BS 著者版 Remark 7.15（著者版 p.62）の分母の違う raw 剰余を比較するための入口。

## 方針

Witt 解からの通常環射を、p と d を殺す条件により二元商へ降ろす。

## 規約

剰余環の非零性・δ 構造・正則性を要求しない。
原典とは異なる具体的 Witt 座標による通常商の比較を行う。

## 使われ方

分母 φ(d) と p の raw 剰余同士に比較射を構成する。
-/

@[expose] public noncomputable section DeltaDivisionPairResidueWitt

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B C σ : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (D : DeltaStructure p A) (c : A) (b : σ → A) (d : A)
local notation "Raw" => DeltaAdjoinDivision D c b
local notation "j" => deltaAdjoinDivisionMap D c b

/-- 概要：raw 除算包を係数の p,d で割る通常商環。
方針：二元生成イデアルの商を取る。
規約：c と d は一致しなくてもよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の未完備二元剰余。 -/
abbrev DeltaDivisionPairResidue := Raw ⧸ Ideal.span {(p : Raw), j d}

/-- 概要：二元剰余への標準係数射。
方針：raw の係数射と商射を合成する。
規約：元の A 係数を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余比較の係数作用。 -/
def deltaDivisionPairResidueBase : A →+* DeltaDivisionPairResidue D c b d :=
  (Ideal.Quotient.mk _).comp j

/-- 概要：raw 二元剰余では p が零。
方針：p の生成イデアルへの所属を使う。
規約：零環も許す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Witt 分母正規化の入力。 -/
theorem deltaDivisionPairResidue_prime_zero : (p : DeltaDivisionPairResidue D c b d) = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {(p : Raw), j d})) (p : Raw) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [map_natCast] using h

/-- 概要：二元剰余の標準係数射は d を殺す。
方針：d の像が生成イデアルに属すことを使う。
規約：除算分母 c とは別に指定した d の消滅。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の単元倍分母公式。 -/
theorem deltaDivisionPairResidueBase_d : deltaDivisionPairResidueBase D c b d d = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- 概要：二元剰余の標準 Witt 点。
方針：raw Witt 点を通常商射で送る。
規約：全ての Witt 座標を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の比較射の生成元。 -/
def deltaDivisionPairResiduePoint (s : σ) : WittVector p (DeltaDivisionPairResidue D c b d) :=
  WittVector.map (Ideal.Quotient.mk _) (deltaDivisionRawWittPoint D c b s)

/-- 概要：Witt ベクトルの通常環射での像は環射の合成と可換。
方針：各係数で定義を確認する。
規約：δ 構造を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Witt 点の逆合成の計算。 -/
theorem witt_map_comp_apply (F : B →+* C) (G : A →+* B) (v : WittVector p A) :
    WittVector.map F (WittVector.map G v) = WittVector.map (F.comp G) v := by
  ext n
  rfl

variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))

include hpA hgL in
/-- 概要：二元剰余の Witt 点は元の全除算方程式を満たす。
方針：raw Witt 点の方程式を商射で送る。
規約：源の p 正則性だけを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母変換に供給する具体的解。 -/
theorem deltaDivisionPairResiduePoint_relation (s : σ) :
    WittVector.map (deltaDivisionPairResidueBase D c b d) (deltaWittGhostVector D c) *
        deltaDivisionPairResiduePoint D c b d s =
      WittVector.map (deltaDivisionPairResidueBase D c b d) (deltaWittGhostVector D (b s)) := by
  have h := congrArg (WittVector.map (Ideal.Quotient.mk (Ideal.span {(p : Raw), j d})))
    (deltaDivisionRawWittPoint_relation D hpA c b hgL s)
  simpa only [map_mul, witt_map_comp_apply, deltaDivisionPairResidueBase,
    deltaDivisionPairResiduePoint] using h

variable (q : A →+* B) (w : σ → WittVector p B)
variable (hpB : (p : B) = 0) (hqd : q d = 0)
variable (hw : ∀ s, WittVector.map q (deltaWittGhostVector D c) * w s =
  WittVector.map q (deltaWittGhostVector D (b s)))

/-- 概要：p,d を殺す係数射と Witt 解から二元剰余への通常環射を作る。
方針：Witt 解の raw 評価が二元イデアルを殺すことを確認する。
規約：終域に δ 構造や非零性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較の両方向の射。 -/
def deltaDivisionPairResidueLift : DeltaDivisionPairResidue D c b d →+* B := by
  let F := deltaDivisionWittMap D hpA q w c b hgL hw
  apply Ideal.Quotient.lift _ F
  have hker : Ideal.span {(p : Raw), j d} ≤ RingHom.ker F := by
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_insert_iff.mp hr with hr | hr
    · subst r
      change F (p : Raw) = 0
      rw [map_natCast]
      exact hpB
    · have hr' : r = j d := Set.mem_singleton_iff.mp hr
      subst r
      change deltaDivisionWittMap D hpA q w c b hgL hw (j d) = 0
      rw [deltaDivisionWittMap_coeff]
      exact hqd
  exact fun r hr => hker hr

/-- 概要：二元剰余からの射は元の係数射を保つ。
方針：商に降ろす前の raw 評価の係数公式を使う。
規約：全ての A の元に対して述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数を保つ比較。 -/
theorem deltaDivisionPairResidueLift_base (r : A) :
    deltaDivisionPairResidueLift D c b d hpA hgL q w hpB hqd hw
      (deltaDivisionPairResidueBase D c b d r) = q r :=
  deltaDivisionWittMap_coeff D hpA q w c b hgL hw r

/-- 概要：二元剰余からの射は指定した全 Witt 解を保つ。
方針：各係数で raw 評価の Witt 点公式を使う。
規約：通常環射の Witt ベクトル写像で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の変数変換を確認する公式。 -/
theorem deltaDivisionPairResidueLift_point (s : σ) :
    WittVector.map (deltaDivisionPairResidueLift D c b d hpA hgL q w hpB hqd hw)
      (deltaDivisionPairResiduePoint D c b d s) = w s := by
  ext n
  exact congrArg (fun z : WittVector p B => z.coeff n)
    (deltaDivisionWittMap_point D hpA q w c b hgL hw s)

include hpA in
/-- 概要：二元剰余の通常環射は係数と全 Witt 点で決まる。
方針：商射の全射性と raw 包の Witt 外延性を使う。
規約：二つの通常環射に δ 互換性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの剰余比較射の両逆合成。 -/
theorem deltaDivisionPairResidueRingHom_ext (f g : DeltaDivisionPairResidue D c b d →+* B)
    (hc : ∀ r, f (deltaDivisionPairResidueBase D c b d r) =
      g (deltaDivisionPairResidueBase D c b d r))
    (hw : ∀ s, WittVector.map f (deltaDivisionPairResiduePoint D c b d s) =
      WittVector.map g (deltaDivisionPairResiduePoint D c b d s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply deltaDivisionRingHom_ext_of_wittPoint D hpA c b
  · exact hc
  · intro s
    simpa only [← witt_map_comp_apply, deltaDivisionPairResiduePoint] using hw s

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionPairResidueWitt

/-! ## Witt 方程式の distinguished 分母の正規化

## 概要

標数 p の環 B への係数射 q が d を殺すとき、qW(φ(d)) は p の単元倍。
BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余と pd 包の比較に使う。

## 方針

W(d) の像の係数を一段ずらした元 v は p v=qW(φ(d)) を満たす。
v の定数係数 q(δd) が単元なので、Witt ベクトルの再帰的逆元を使う。

## 規約

源は p 正則、d は distinguished とし、終域に δ 構造を要求しない。
原典とは異なる具体的 Witt 方程式による分母変換である。

## 使われ方

φ(d) による除算方程式の解を p による除算方程式の解へ可逆に移す。
-/

@[expose] public noncomputable section DistinguishedWittDenominator

namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B] [CharP B p]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (q : A →+* B) (d : A) (hd : D.IsDistinguished d)

omit [CharP B p] in
include hpA hd in
/-- 概要：d の Witt 除算解の定数係数は単元。
方針：定数係数を q(δd) と計算し distinguished 性を送る。
規約：源の p 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母の単元倍への正規化。 -/
theorem distinguishedWittDenominator_coeff_zero_isUnit :
    IsUnit ((deltaPDivisionWittResidueSolution D q d).coeff 0) := by
  rw [deltaPDivisionWittResidueSolution_coeff_zero D q d hpA]
  exact hd.map q

/-- 概要：係数をずらした Witt 元をそのまま値に持つ単元。
方針：定数係数の単元性を Witt ベクトルの再帰的逆元へ渡す。
規約：単元の値を具体的な Witt 解のまま保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の除算変数の可逆な変換。 -/
def distinguishedWittDenominatorUnit : (WittVector p B)ˣ :=
  WittVector.mkUnit
    (distinguishedWittDenominator_coeff_zero_isUnit D hpA q d hd).unit_spec.symm

/-- 概要：選んだ単元の値は既存の具体的 Witt 除算解。
方針：Witt 単元の定義を使う。
規約：選択に依存しない値の等式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数公式との接続。 -/
theorem distinguishedWittDenominatorUnit_val :
    (distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) =
      deltaPDivisionWittResidueSolution D q d := rfl

/-- 概要：d を殺す係数射の下で φ(d) の全 Witt 像は p の単元倍。
方針：具体的 Witt 解の除算方程式を使う。
規約：ghost 射の単射性と q(d)=0 を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 分母を p に変換する計算。 -/
theorem distinguishedWittDenominatorUnit_mul
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqd : q d = 0) :
    (p : WittVector p B) * distinguishedWittDenominatorUnit D hpA q d hd =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift d)) :=
  deltaPDivisionWittResidueSolution_mul D q d hgA hqd

/-- 概要：φ(d) による Witt 除算解と p による除算解は同値。
方針：単元 v による乗法と v⁻¹ による乗法を逆にする。
規約：右辺 z は任意の Witt 元で、終域の δ 構造を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 包比較に供給する Witt 解の変換。 -/
def distinguishedWittDivisionSolutionEquiv
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqd : q d = 0) (z : WittVector p B) :
    {w : WittVector p B //
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift d)) * w = z} ≃
    {w : WittVector p B // (p : WittVector p B) * w = z} where
  toFun w := ⟨(distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) * w, by
    rw [← mul_assoc, distinguishedWittDenominatorUnit_mul D hpA q d hd hgA hqd]
    exact w.property⟩
  invFun w := ⟨(↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B) * w, by
    rw [← distinguishedWittDenominatorUnit_mul D hpA q d hd hgA hqd]
    rw [mul_assoc, ← mul_assoc
      (distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B)
      (↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B)
      (w : WittVector p B), Units.mul_inv, one_mul]
    exact w.property⟩
  left_inv w := by
    apply Subtype.ext
    change (↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B) *
      ((distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) * w) = w
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv w := by
    apply Subtype.ext
    change (distinguishedWittDenominatorUnit D hpA q d hd : WittVector p B) *
      ((↑((distinguishedWittDenominatorUnit D hpA q d hd)⁻¹) : WittVector p B) * w) = w
    rw [← mul_assoc, Units.mul_inv, one_mul]

end SerrePositivity.BhattScholze.Andre

end DistinguishedWittDenominator

/-! ## 分母正規化単元の零環を含む自然性

## 概要

p=0 の任意の係数商で分母正規化単元を作り、通常環射での自然性を示す。
BS 著者版 Remark 7.15（著者版 p.62）の二つの raw 剰余の逆比較に用いる。

## 方針

非零環では既存の Witt 単元を使い、零環では全 Witt 元の一致を使う。
値は係数を一段ずらす具体式なので通常環射で保たれる。

## 規約

標数が正確に p であることや非零環であることを商に要求しない。

## 使われ方

剰余比較の両逆合成で、単元とその逆元の像を照合する。
-/

@[expose] public noncomputable section DistinguishedWittDenominatorNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (q : A →+* B) (d : A) (hd : D.IsDistinguished d)

include hpA hd in
/-- 概要：p が零の係数環では分母の具体的 Witt 解は単元。
方針：非零環で標数 p の単元構成を使い、零環の場合を別に処理する。
規約：商が零環であってもよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の任意の raw 剰余での分母変換。 -/
theorem distinguishedWittDenominator_isUnit_of_prime_zero (hpB : (p : B) = 0) :
    IsUnit (deltaPDivisionWittResidueSolution D q d) := by
  classical
  by_cases hB : Nontrivial B
  · let := hB
    let : CharP B p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpB
    exact (distinguishedWittDenominatorUnit D hpA q d hd).isUnit
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hB
    have hz : deltaPDivisionWittResidueSolution D q d = 1 := by
      ext n
      exact Subsingleton.elim _ _
    rw [hz]
    exact isUnit_one

/-- 概要：p が零の任意の係数商における分母正規化単元。
方針：具体的 Witt 解の単元性から選ぶ。
規約：値はその具体的 Witt 解を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余の変数変換。 -/
def distinguishedWittResidueUnit (hpB : (p : B) = 0) : (WittVector p B)ˣ :=
  (distinguishedWittDenominator_isUnit_of_prime_zero D hpA q d hd hpB).unit

/-- 概要：零環を含む正規化単元の値は具体的な係数ずらし。
方針：選んだ単元の仕様を使う。
規約：非零性の分岐に依存しない値の等式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常環射での自然性。 -/
theorem distinguishedWittResidueUnit_val (hpB : (p : B) = 0) :
    (distinguishedWittResidueUnit D hpA q d hd hpB : WittVector p B) =
      deltaPDivisionWittResidueSolution D q d :=
  (distinguishedWittDenominator_isUnit_of_prime_zero D hpA q d hd hpB).unit_spec

/-- 概要：p が零の任意の係数商で φ(d) の Witt 像は p の単元倍。
方針：単元の値を具体的 Witt 解へ戻して除算公式を使う。
規約：q(d)=0 と源 ghost 射の単射性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 分母の置き換え。 -/
theorem distinguishedWittResidueUnit_mul (hpB : (p : B) = 0)
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqd : q d = 0) :
    (p : WittVector p B) * distinguishedWittResidueUnit D hpA q d hd hpB =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift d)) := by
  rw [distinguishedWittResidueUnit_val]
  exact deltaPDivisionWittResidueSolution_mul D q d hgA hqd

/-- 概要：正規化単元の値は係数射を保つ任意の通常環射で保たれる。
方針：具体的な全係数の式で確認する。
規約：二つの終域は p が零の可換環。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の比較射の逆合成。 -/
theorem distinguishedWittResidueUnit_map (hpB : (p : B) = 0)
    (q' : A →+* C) (hpC : (p : C) = 0) (F : B →+* C) (hF : F.comp q = q') :
    WittVector.map F (distinguishedWittResidueUnit D hpA q d hd hpB : WittVector p B) =
      (distinguishedWittResidueUnit D hpA q' d hd hpC : WittVector p C) := by
  rw [distinguishedWittResidueUnit_val, distinguishedWittResidueUnit_val]
  ext n
  rw [WittVector.map_coeff, deltaPDivisionWittResidueSolution_coeff,
    deltaPDivisionWittResidueSolution_coeff]
  exact RingHom.congr_fun hF _

/-- 概要：正規化単元そのものも通常環射で保たれる。
方針：単元の値の外延性を使う。
規約：単元群への写像で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の逆元の自然性への入力。 -/
theorem distinguishedWittResidueUnit_map_units (hpB : (p : B) = 0)
    (q' : A →+* C) (hpC : (p : C) = 0) (F : B →+* C) (hF : F.comp q = q') :
    Units.map (WittVector.map F).toMonoidHom (distinguishedWittResidueUnit D hpA q d hd hpB) =
      distinguishedWittResidueUnit D hpA q' d hd hpC := by
  apply Units.ext
  exact distinguishedWittResidueUnit_map D hpA q d hd hpB q' hpC F hF

/-- 概要：正規化単元の逆元の値も通常環射で保たれる。
方針：単元群の写像が逆元を保つことを使う。
規約：逆元は単元群で取り、その値を Witt 環へ送る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の変数変換の両逆合成。 -/
theorem distinguishedWittResidueUnit_inv_map (hpB : (p : B) = 0)
    (q' : A →+* C) (hpC : (p : C) = 0) (F : B →+* C) (hF : F.comp q = q') :
    WittVector.map F (↑((distinguishedWittResidueUnit D hpA q d hd hpB)⁻¹) : WittVector p B) =
      (↑((distinguishedWittResidueUnit D hpA q' d hd hpC)⁻¹) : WittVector p C) := by
  have hv := distinguishedWittResidueUnit_map D hpA q d hd hpB q' hpC F hF
  have hi : WittVector.map F
      (↑((distinguishedWittResidueUnit D hpA q d hd hpB)⁻¹) : WittVector p B) *
        (distinguishedWittResidueUnit D hpA q' d hd hpC : WittVector p C) = 1 := by
    rw [← hv, ← map_mul, Units.inv_mul, map_one]
  calc
    _ = WittVector.map F
        (↑((distinguishedWittResidueUnit D hpA q d hd hpB)⁻¹) : WittVector p B) *
        ((distinguishedWittResidueUnit D hpA q' d hd hpC : WittVector p C) *
          (↑((distinguishedWittResidueUnit D hpA q' d hd hpC)⁻¹) : WittVector p C)) := by
      rw [Units.mul_inv, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

end SerrePositivity.BhattScholze.Andre

end DistinguishedWittDenominatorNaturality

/-! ## Frobenius 分母の raw 剰余と p 除算剰余

## 概要

distinguished d に対し A{b/φ(d)}/(p,d) と A{b/p}/(p,d) は A 係数を保って環同型。
BS 著者版 Remark 7.15（著者版 p.62）の具体的 pd 包比較のための分母変換。

## 方針

各剰余の標準 Witt 点を分母正規化単元とその逆元で変換する。
通常 Witt 普遍性で環射を作り、係数と全 Witt 点で両逆合成を確認する。

## 規約

源の p 正則性と ghost 単射性を明示し、分子族 b の形は限定しない。
原典とは異なる通常 Witt 解による証明である。

## 使われ方

実完備化から得た Frobenius 側 raw 剰余を、既存の pd 表示に接続する。
-/

@[expose] public noncomputable section DeltaDivisionFrobeniusPResidueEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (hd : D.IsDistinguished d) (b : σ → A)
local notation "Qφ" => DeltaDivisionPairResidue D (D.frobeniusLift d) b d
local notation "Qp" => DeltaDivisionPairResidue D (p : A) b d
local notation "qφ" => deltaDivisionPairResidueBase D (D.frobeniusLift d) b d
local notation "qp" => deltaDivisionPairResidueBase D (p : A) b d
local notation "wφ" => deltaDivisionPairResiduePoint D (D.frobeniusLift d) b d
local notation "wp" => deltaDivisionPairResiduePoint D (p : A) b d
local notation "hpφ" => deltaDivisionPairResidue_prime_zero D (D.frobeniusLift d) b d
local notation "hpp" => deltaDivisionPairResidue_prime_zero D (p : A) b d
local notation "vφ" => distinguishedWittResidueUnit D hpA qφ d hd hpφ
local notation "vp" => distinguishedWittResidueUnit D hpA qp d hd hpp

include hgA in
/-- 概要：通常係数射で自然数 p の全 Witt 像は Witt 環の p。
方針：Witt 環射の自然数保存を使う。
規約：元の通常係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaWitt_prime_image {B : Type u} [CommRing B] (q : A →+* B) :
    WittVector.map q (deltaWittGhostVector D (p : A)) = (p : WittVector p B) := by
  change WittVector.map q (deltaWittGhostRingHom D hgA (p : A)) = _
  rw [map_natCast, map_natCast]

include hpA hgA hgL in
/-- 概要：p 分母の二元剰余の Witt 点は p 除算方程式を満たす。
方針：標準 raw 方程式の分母像を p と計算する。
規約：元の通常係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionPResiduePoint_relation (s : σ) :
    (p : WittVector p Qp) * wp s = WittVector.map qp (deltaWittGhostVector D (b s)) := by
  have h := deltaDivisionPairResiduePoint_relation D (p : A) b d hpA hgL s
  rw [deltaWitt_prime_image D hgA] at h
  exact h

include hgA hgL in
/-- 概要：p 側の Witt 点を単元の逆元で変換すると Frobenius 分母の解になる。
方針：Frobenius 分母の p 単元倍表示を使う。
規約：元の通常係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionFrobeniusToPResiduePoint_relation (s : σ) :
    WittVector.map qp (deltaWittGhostVector D (D.frobeniusLift d)) *
        ((↑(vp⁻¹) : WittVector p Qp) * wp s) =
      WittVector.map qp (deltaWittGhostVector D (b s)) := by
  rw [← distinguishedWittResidueUnit_mul D hpA qp d hd hpp hgA
    (deltaDivisionPairResidueBase_d D (p : A) b d)]
  rw [mul_assoc, ← mul_assoc (vp : WittVector p Qp) (↑(vp⁻¹) : WittVector p Qp)
    (wp s), Units.mul_inv, one_mul]
  exact deltaDivisionPResiduePoint_relation D hpA hgA hgL d b s

include hgA hgL in
/-- 概要：Frobenius 側の Witt 点を単元倍すると p 分母の解になる。
方針：分母の単元倍公式と元の方程式を使う。
規約：元の通常係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionPToFrobeniusResiduePoint_relation (s : σ) :
    WittVector.map qφ (deltaWittGhostVector D (p : A)) *
        ((vφ : WittVector p Qφ) * wφ s) =
      WittVector.map qφ (deltaWittGhostVector D (b s)) := by
  rw [deltaWitt_prime_image D hgA, ← mul_assoc,
    distinguishedWittResidueUnit_mul D hpA qφ d hd hpφ hgA
      (deltaDivisionPairResidueBase_d D (D.frobeniusLift d) b d)]
  exact deltaDivisionPairResiduePoint_relation D (D.frobeniusLift d) b d hpA hgL s

/-- 概要：Frobenius 分母の二元剰余から p 分母の二元剰余への通常環射。
方針：p 側の Witt 点を正規化単元の逆元で変換する。
規約：元の係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較の順射。 -/
def deltaDivisionFrobeniusToPResidueMap : Qφ →+* Qp := by
  exact deltaDivisionPairResidueLift D (D.frobeniusLift d) b d hpA hgL qp
    (fun s => (↑(vp⁻¹) : WittVector p Qp) * wp s) hpp
    (deltaDivisionPairResidueBase_d D (p : A) b d)
    (deltaDivisionFrobeniusToPResiduePoint_relation D hpA hgA hgL d hd b)

/-- 概要：p 分母の二元剰余から Frobenius 分母の二元剰余への通常環射。
方針：Frobenius 側の Witt 点を正規化単元で変換する。
規約：元の係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較の逆射。 -/
def deltaDivisionPToFrobeniusResidueMap : Qp →+* Qφ := by
  exact deltaDivisionPairResidueLift D (p : A) b d hpA hgL qφ
    (fun s => (vφ : WittVector p Qφ) * wφ s) hpφ
    (deltaDivisionPairResidueBase_d D (D.frobeniusLift d) b d)
    (deltaDivisionPToFrobeniusResiduePoint_relation D hpA hgA hgL d hd b)

local notation "F" => deltaDivisionFrobeniusToPResidueMap D hpA hgA hgL d hd b
local notation "G" => deltaDivisionPToFrobeniusResidueMap D hpA hgA hgL d hd b

/-- 概要：順比較射は元の全係数を保つ。
方針：二元商への Witt 評価の係数公式を使う。
規約：全ての r∈A に対して述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用の確認。 -/
theorem deltaDivisionFrobeniusToPResidueMap_base (r : A) : F (qφ r) = qp r :=
  deltaDivisionPairResidueLift_base _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：逆比較射も元の全係数を保つ。
方針：二元商への Witt 評価の係数公式を使う。
規約：全ての r∈A に対して述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の逆比較の係数作用。 -/
theorem deltaDivisionPToFrobeniusResidueMap_base (r : A) : G (qp r) = qφ r :=
  deltaDivisionPairResidueLift_base _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：順比較射は全 Witt 点を正規化単元の逆元倍へ送る。
方針：二元商への Witt 評価の点公式を使う。
規約：全 Witt 係数を同時に追う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の逆合成の計算。 -/
theorem deltaDivisionFrobeniusToPResidueMap_point (s : σ) :
    WittVector.map F (wφ s) = (↑(vp⁻¹) : WittVector p Qp) * wp s :=
  deltaDivisionPairResidueLift_point _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：逆比較射は全 Witt 点を正規化単元倍へ送る。
方針：二元商への Witt 評価の点公式を使う。
規約：全 Witt 係数を同時に追う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のもう一方の逆合成の計算。 -/
theorem deltaDivisionPToFrobeniusResidueMap_point (s : σ) :
    WittVector.map G (wp s) = (vφ : WittVector p Qφ) * wφ s :=
  deltaDivisionPairResidueLift_point _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：順射と元の係数射の合成は p 側の係数射。
方針：全係数上の公式で外延性を使う。
規約：元の通常係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionFrobeniusToPResidueMap_comp_base : (F).comp qφ = qp := by
  ext r
  exact deltaDivisionFrobeniusToPResidueMap_base D hpA hgA hgL d hd b r

/-- 概要：逆射と元の係数射の合成は Frobenius 側の係数射。
方針：全係数上の公式で外延性を使う。
規約：元の通常係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionPToFrobeniusResidueMap_comp_base : (G).comp qp = qφ := by
  ext r
  exact deltaDivisionPToFrobeniusResidueMap_base D hpA hgA hgL d hd b r

/-- 概要：逆射の後に順射を適用する合成は p 側の恒等射。
方針：係数と全 Witt 点で単元の自然性と逆元による相殺を使う。
規約：零環の場合も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余同型の片側逆。 -/
theorem deltaDivisionFrobeniusPResidue_comp : (F).comp G = RingHom.id Qp := by
  apply deltaDivisionPairResidueRingHom_ext D (p : A) b d hpA
  · intro r
    change F (G (qp r)) = qp r
    rw [deltaDivisionPToFrobeniusResidueMap_base, deltaDivisionFrobeniusToPResidueMap_base]
  · intro s
    rw [← witt_map_comp_apply, deltaDivisionPToFrobeniusResidueMap_point, map_mul,
      distinguishedWittResidueUnit_map D hpA qφ d hd hpφ qp hpp F
        (deltaDivisionFrobeniusToPResidueMap_comp_base D hpA hgA hgL d hd b),
      deltaDivisionFrobeniusToPResidueMap_point]
    change (vp : WittVector p Qp) * ((↑(vp⁻¹) : WittVector p Qp) * wp s) = wp s
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- 概要：順射の後に逆射を適用する合成は Frobenius 側の恒等射。
方針：全 Witt 点で逆単元の自然性と相殺を使う。
規約：通常環射の外延性に帰着する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余同型のもう片側逆。 -/
theorem deltaDivisionPFrobeniusResidue_comp : (G).comp F = RingHom.id Qφ := by
  apply deltaDivisionPairResidueRingHom_ext D (D.frobeniusLift d) b d hpA
  · intro r
    change G (F (qφ r)) = qφ r
    rw [deltaDivisionFrobeniusToPResidueMap_base, deltaDivisionPToFrobeniusResidueMap_base]
  · intro s
    rw [← witt_map_comp_apply, deltaDivisionFrobeniusToPResidueMap_point, map_mul,
      distinguishedWittResidueUnit_inv_map D hpA qp d hd hpp qφ hpφ G
        (deltaDivisionPToFrobeniusResidueMap_comp_base D hpA hgA hgL d hd b),
      deltaDivisionPToFrobeniusResidueMap_point]
    change (↑(vφ⁻¹) : WittVector p Qφ) * ((vφ : WittVector p Qφ) * wφ s) = wφ s
    rw [← mul_assoc, Units.inv_mul, one_mul]

/-- 概要：distinguished 元の Frobenius 分母の raw 剰余は p 分母の raw 剰余と環同型。
方針：Witt 単元変換で構成した二つの通常環射と両逆合成を束ねる。
規約：分子族の形・モニック性・有限性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的 pd 表示への分母の接続。 -/
def deltaDivisionFrobeniusPResidueEquiv : Qφ ≃+* Qp :=
  RingEquiv.ofRingHom F G
    (deltaDivisionFrobeniusPResidue_comp D hpA hgA hgL d hd b)
    (deltaDivisionPFrobeniusResidue_comp D hpA hgA hgL d hd b)

/-- 概要：分母変換の環同型は元の全係数を保つ。
方針：順比較射の係数公式を使う。
規約：元の A 係数作用に関する同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包比較へ係数を保って合成する。 -/
theorem deltaDivisionFrobeniusPResidueEquiv_base (r : A) :
    deltaDivisionFrobeniusPResidueEquiv D hpA hgA hgL d hd b (qφ r) = qp r :=
  deltaDivisionFrobeniusToPResidueMap_base D hpA hgA hgL d hd b r

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFrobeniusPResidueEquiv

/-! ## raw p 除算包の係数商と主 pd 表示

## 概要

正則な一元入力について、raw φ(y)/p 包の任意の係数商は係数商上の主分冪表示と環同型。
BS 著者版 Corollary 2.39（著者版 p.25）と BS 著者版 Remark 7.15（p.62）の具体的剰余比較。

## 方針

既存の raw 包と主分冪表示の係数を保つ同型を商へ降ろし、表示の係数商と交換する。

## 規約

p 局所性・源の p 正則性・y mod p の正則性を明示する。
任意の係数イデアルに正則性は要求しない。実分冪構造の構成は別工程。

## 使われ方

Frobenius 分母を正規化した二元剰余を具体的 pd 包の台環へ移す。
-/

@[expose] public noncomputable section DeltaPDivisionIdealPDComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun r : A => (p : A) * r))
variable (D : DeltaStructure p A) (y : A)
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a" => fun _ : σ => D.frobeniusLift y
local notation "Raw" => DeltaAdjoinDivision D (p : A) a
local notation "j" => deltaAdjoinDivisionMap D (p : A) a
local notation "PD" => PrincipalDPPresentation A y
local notation "E" => _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv hA hpA D y hgL v hv hy

/-- 概要：raw p 除算と主分冪表示の同型は任意の係数イデアルの像を保つ。
方針：元の A 上の全係数公式から環射の合成を照合する。
規約：係数イデアル K は任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二元商への同型の降下。 -/
theorem deltaPDivisionIdealPD_map (K : Ideal A) :
    (K.map j).map (E).toRingHom = K.map (algebraMap A PD) := by
  rw [Ideal.map_map]
  congr 1
  ext r
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv_coeff hA hpA D y hgL v hv hy r

/-- 概要：raw p 除算包の係数イデアル商は係数商上の主分冪表示と環同型。
方針：raw 同型を商へ降ろし、主分冪表示と係数商の交換を合成する。
規約：モニック性ではなく y mod p の正則性を入力とする。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）、BS 著者版 Remark 7.15（p.62）の具体的 pd 台環比較。 -/
def deltaPDivisionIdealPDEquiv (K : Ideal A) :
    (Raw ⧸ K.map j) ≃+*
      PrincipalDPPresentation (A ⧸ K) (Ideal.Quotient.mk K y) :=
  (Ideal.quotientEquiv _ _ E (deltaPDivisionIdealPD_map hA hpA D y hgL v hv hy K).symm).trans
    (principalDPIdealQuotientEquiv K y)

/-- 概要：係数商を通る raw-pd 同型は元の全係数を保つ。
方針：商の代表元公式と両同型の係数公式を合成する。
規約：全ての r∈A を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数の Frobenius 作用の追跡。 -/
theorem deltaPDivisionIdealPDEquiv_coeff (K : Ideal A) (r : A) :
    deltaPDivisionIdealPDEquiv hA hpA D y hgL v hv hy K (Ideal.Quotient.mk _ (j r)) =
      algebraMap (A ⧸ K) _ (Ideal.Quotient.mk K r) := by
  rw [deltaPDivisionIdealPDEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv_coeff, principalDPIdealQuotientEquiv_coeff]

/-- 概要：raw-pd 係数商同型は具体的な階乗生成元を標準分冪へ送る。
方針：raw 同型と主分冪係数商の生成元公式を使う。
規約：全ての次数 n を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実分冪構造を移送するための公式。 -/
theorem deltaPDivisionIdealPDEquiv_factorial (K : Ideal A) (n : ℕ) :
    deltaPDivisionIdealPDEquiv hA hpA D y hgL v hv hy K
      (Ideal.Quotient.mk _
        (deltaPDivisionRawFactorialQuotient D (fun _ : σ => y) hA (default : σ) n)) =
      principalDPGenerator (Ideal.Quotient.mk K y) n := by
  rw [deltaPDivisionIdealPDEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRawPrincipalEquiv_factorial, principalDPIdealQuotientEquiv_generator]

/-- 概要：raw p 除算の二元剰余は A/(p,d) 上の主分冪表示と環同型。
方針：二元生成イデアルを元の係数イデアルの像と同定し、一般比較を適用する。
規約：d の distinguished 性はこの比較には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化剰余との接続。 -/
def deltaPDivisionPairPDEquiv (d : A) :
    DeltaDivisionPairResidue D (p : A) a d ≃+*
      PrincipalDPPresentation (A ⧸ Ideal.span {(p : A), d})
        (Ideal.Quotient.mk (Ideal.span {(p : A), d}) y) :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : Raw), j d} =
    (Ideal.span {(p : A), d}).map j by
      rw [Ideal.map_span, Set.image_pair, map_natCast])).trans
    (deltaPDivisionIdealPDEquiv hA hpA D y hgL v hv hy (Ideal.span {(p : A), d}))

/-- 概要：二元剰余の raw-pd 同型は元の全係数を保つ。
方針：像イデアルの書換えと一般係数商の係数公式を使う。
規約：元の自然な係数射について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の係数作用の移送。 -/
theorem deltaPDivisionPairPDEquiv_coeff (d r : A) :
    deltaPDivisionPairPDEquiv hA hpA D y hgL v hv hy d
        (deltaDivisionPairResidueBase D (p : A) a d r) =
      algebraMap (A ⧸ Ideal.span {(p : A), d}) _
        (Ideal.Quotient.mk (Ideal.span {(p : A), d}) r) := by
  change deltaPDivisionPairPDEquiv hA hpA D y hgL v hv hy d
    (Ideal.Quotient.mk _ (j r)) = _
  rw [deltaPDivisionPairPDEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact deltaPDivisionIdealPDEquiv_coeff hA hpA D y hgL v hv hy _ r

end SerrePositivity.BhattScholze.Andre

end DeltaPDivisionIdealPDComparison

/-! ## 有限 δ 関係商の mod p と最高変数の正則性

## 概要

有限 raw δ 関係商を mod p で初期係数商と後続変数へ分離する。
そこで d が正則なら次の δ 関係も正則となる。
BS 著者版 Remark 7.15（著者版 p.62）の源の p 正則性に向けた有限段の計算。

## 方針

p を初期変数環のイデアルへ含めて既存の変数分離を使う。
次関係の先頭係数 φ^(N+1)(d) は mod p で d^(p^(N+1)) となる。

## 規約

全有限段の正則性を結論する段階ではなく、帰納法の次段を供給する。
prismatic 完備化や原典の T との同定は別工程。

## 使われ方

有限商の p 正則性と mod p の d 正則性の同時帰納法。
-/

@[expose] public noncomputable section DeltaDivisionFiniteModPrimeTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B₀" => MvPolynomial (σ × Fin (N + 1)) A
local notation "J₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteStageInitialIdeal D d a N
local notation "Jp" => Ideal.span {(p : B₀)} ⊔ J₀
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I₀

/-- 概要：初期有限関係と p のイデアルの拡張は全自由環の同じイデアル。
方針：既存の初期関係の像と環射の自然数保存を使う。
規約：添字型の有限性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限 mod p 商の分離。 -/
theorem deltaDivisionFiniteModPrimeInitialIdeal_map :
    (Jp).map (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom = Ip := by
  rw [Ideal.map_sup, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteStageInitialIdeal_map,
    Ideal.map_span, Set.image_singleton, map_natCast]

/-- 概要：有限関係商の mod p は初期 mod p 商上の後続多項式環と環同型。
方針：初期イデアルの像を照合して既存の任意初期商比較を適用する。
規約：一重イデアル商として mod p を表す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次関係の先頭係数計算。 -/
def deltaDivisionFiniteModPrimeTailEquiv :
    (L₀ ⧸ Ip) ≃+* MvPolynomial (σ × ℕ) (B₀ ⧸ Jp) :=
  (Ideal.quotEquivOfEq (deltaDivisionFiniteModPrimeInitialIdeal_map D d a N).symm).trans
    (_root_.SerrePositivity.BhattScholze.Andre.relativeFreeFiniteInitialQuotientEquiv (N + 1) Jp)

/-- 概要：有限 mod p 分離同型の代表元公式。
方針：初期商比較の代表元公式を使う。
規約：全自由環の全ての元を含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数と次関係の照合。 -/
theorem deltaDivisionFiniteModPrimeTailEquiv_mk (f : L₀) :
    deltaDivisionFiniteModPrimeTailEquiv D d a N (Ideal.Quotient.mk Ip f) =
      MvPolynomial.map (Ideal.Quotient.mk Jp)
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 1) σ A f) := by
  rw [deltaDivisionFiniteModPrimeTailEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, _root_.SerrePositivity.BhattScholze.Andre.relativeFreeFiniteInitialQuotientEquiv_mk]

/-- 概要：有限 mod p 分離同型は元の A 係数を初期係数商へ送る。
方針：変数分離と多項式写像の係数公式を使う。
規約：元の標準係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の d 正則性の降下。 -/
theorem deltaDivisionFiniteModPrimeTailEquiv_coeff (r : A) :
    deltaDivisionFiniteModPrimeTailEquiv D d a N (Ideal.Quotient.mk Ip (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk Jp (MvPolynomial.C r)) := by
  rw [deltaDivisionFiniteModPrimeTailEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_C, MvPolynomial.map_C]

/-- 概要：次の δ 関係は有限 mod p 分離後も最高変数の一次式。
方針：既存の先頭項と下位項の分解を通常商へ送る。
規約：最高係数を φ^(N+1)(d) の像のまま表示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次関係の正則性。 -/
theorem deltaDivisionFiniteModPrimeTailEquiv_next (s : σ) :
    deltaDivisionFiniteModPrimeTailEquiv D d a N
      (Ideal.Quotient.mk Ip (deltaDivisionIteratedRelation D d a s (N + 1))) =
        MvPolynomial.C (Ideal.Quotient.mk Jp (MvPolynomial.C (D.frobeniusLift^[N + 1] d))) *
          MvPolynomial.X (s, 0) +
        MvPolynomial.C (Ideal.Quotient.mk Jp
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1))) := by
  rw [deltaDivisionFiniteModPrimeTailEquiv_mk,
    deltaDivisionIteratedRelation_eq_leading_add_lower]
  have hx := relativeFreeFiniteVariableSplitAlgEquiv_X_tail (N + 1) σ A s 0
  simp only [zero_add] at hx
  rw [map_add, map_mul, relativeFreeFiniteVariableSplitAlgEquiv_C, hx,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, map_add, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFiniteModPrimeTail

/-! ## 元の raw δ 割り算包の実完備化の普遍性

## 概要

分母の像が正則で分子族がその像で割り切れる δ 射は、元の raw 包の実完備化から
一意に延長する。BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の envelope 比較への入口。

## 方針

正則分母への raw δ 割り算の一意延長と、実二座標完備化の δ 一意延長を合成する。

## 規約

元の raw 包をねじれ除去商へ変更しない。試験環の p と分母像の導来完備性を明示する。

## 使われ方

具体的な実完備化 prism の普遍性を、基底射を保った比較へ接続する。
-/

@[expose] public noncomputable section RawDeltaDivisionPDUniversal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R σ T : Type u} [CommRing R] [CommRing T]

/-- 概要：正則な分母像と分子の可除性を持つ完備 δ 試験環へ、raw 実完備化から一意に延長する。
方針：raw δ 割り算と実完備化の二つの一意延長を結ぶ。
規約：試験環の p ねじれを制限せず、分母の正則性を明示する。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の元の envelope の比較。 -/
theorem existsUnique_rawDeltaDivisionPDHom
    (D : DeltaStructure p R) (E : DeltaStructure p T) (d : R) (a : σ → R)
    (f : R →+* T) (hf : D.IsDeltaHom E f)
    (hreg : Function.Injective (fun x : T => f d * x)) (ha : ∀ s, f d ∣ f (a s))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (f d) (ModuleCat.of T T)) :
    let B := DeltaAdjoinDivision D d a
    let j := deltaAdjoinDivisionMap D d a
    let := pdCompletionCommRing B p (j d)
    ∃! h : PDCompletionH0 B p (j d) →+* T,
      (deltaPDCompletionStructure (deltaAdjoinDivisionStructure D d a) (j d)).IsDeltaHom E h ∧
        h.comp ((pdCompletionUnit B p (j d)).comp j) = f := by
  let B := DeltaAdjoinDivision D d a
  let DB := deltaAdjoinDivisionStructure D d a
  let j := deltaAdjoinDivisionMap D d a
  let := pdCompletionCommRing B p (j d)
  let c := pdCompletionUnit B p (j d)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D E d a f hf hreg ha
  have hkd : k (j d) = f d := RingHom.congr_fun hk.2 d
  have hd' : IsModuleComplete T (k (j d)) (ModuleCat.of T T) := by rw [hkd]; exact hd
  obtain ⟨h, hh, hu⟩ := existsUnique_deltaPDCompletionHom DB (j d) E k hk.1 hp hd'
  refine ⟨h, ⟨hh.1, ?_⟩, ?_⟩
  · change h.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hh.2, hk.2]
  · intro l hl
    apply hu l
    refine ⟨hl.1, ?_⟩
    apply hku (l.comp c)
    refine ⟨hl.1.comp (pdCompletionUnit_isDeltaHom DB (j d)), ?_⟩
    change (l.comp c).comp j = f
    rw [RingHom.comp_assoc]
    exact hl.2

end SerrePositivity.BhattScholze.Andre

end RawDeltaDivisionPDUniversal

/-! ## 正則な実 raw 完備化と旧ねじれ除去後の実完備化

## 概要

元の raw 包の実完備化で分母像が正則なら、旧分母ねじれの δ 閉包商を先に挟んだ
実完備化と標準 raw 射を保つ環同型となる。
BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の二つの具体的構成の比較。

## 方針

元の実完備化への標準 δ 射は旧ねじれの δ 閉包を殺す。
商からの射を実完備化へ延長し、逆合成を実完備化の環普遍性と商射の全射性で確認する。

## 規約

旧ねじれ除去後の実完備化に新たな正則性を仮定しない。

## 使われ方

無限根モニックの元の実候補を既存の BS 著者版 Proposition 7.2 の一段構成へ同定する。
-/

@[expose] public noncomputable section RawDeltaDivisionPDTorsionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R σ : Type u} [CommRing R]
variable (D : DeltaStructure p R) (d : R) (a : σ → R)
local notation "B" => DeltaAdjoinDivision D d a
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "j" => deltaAdjoinDivisionMap D d a
local notation "H" => PDCompletionH0 B p (j d)
local notation "uB" => pdCompletionUnit B p (j d)
local notation "DH" => deltaPDCompletionStructure DB (j d)
local notation "U" => DeltaDivisionTorsionQuotient D d a
local notation "q" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure DB (RingHom.ker (algebraMap B (Localization.Away (j d)))))
local notation "jU" => deltaDivisionTorsionMap D d a
local notation "HU" => DerivedDeltaDivisionCompletion D d a
local notation "uU" => pdCompletionUnit U p (jU d)

/-- 概要：元の実 raw 完備化の分母が正則なら旧ねじれ除去を挟む実完備化と環同型。
方針：旧ねじれ商を通る標準射を延長し、係数上の逆合成から完備化の一意性を使う。
規約：新しい正則性は元の実 H⁰ の分母像だけに仮定する。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の一段構成比較。 -/
def rawDeltaDivisionPDTorsionEquiv
    (hreg : let := pdCompletionCommRing B p (j d)
      Function.Injective (fun x : H => uB (j d) * x)) :
    let := pdCompletionCommRing B p (j d)
    let := derivedDeltaDivisionCommRing D d a
    H ≃+* HU := by
  let := pdCompletionCommRing B p (j d)
  let := derivedDeltaDivisionCommRing D d a
  let kB : B →+* HU := (uU).comp q
  have hdB : kB (j d) = derivedDeltaDivisionMap D d a d := rfl
  have hcB : IsModuleComplete HU (kB (j d)) (ModuleCat.of HU HU) := by
    rw [hdB]
    exact derivedDeltaDivision_complete_d D d a
  let F := (existsUnique_pdCompletionRingHom B p (j d) HU kB
    (derivedDeltaDivision_complete_p D d a) hcB).choose
  have hF : F.comp uB = kB := (existsUnique_pdCompletionRingHom B p (j d) HU kB
    (derivedDeltaDivision_complete_p D d a) hcB).choose_spec.1
  let kU := ((DB).existsUnique_torsionReductionHom (j d) DH uB
    (pdCompletionUnit_isDeltaHom DB (j d)) hreg).choose
  have hkU : kU.comp q = uB := ((DB).existsUnique_torsionReductionHom (j d) DH uB
    (pdCompletionUnit_isDeltaHom DB (j d)) hreg).choose_spec.1.1
  have hdU : kU (jU d) = uB (j d) := RingHom.congr_fun hkU (j d)
  have hcU : IsModuleComplete H (kU (jU d)) (ModuleCat.of H H) := by
    rw [hdU]
    exact pdCompletionH0_self_complete_d B p (j d)
  let G := (existsUnique_pdCompletionRingHom U p (jU d) H kU
    (pdCompletionH0_self_complete_p B p (j d)) hcU).choose
  have hG : G.comp uU = kU := (existsUnique_pdCompletionRingHom U p (jU d) H kU
    (pdCompletionH0_self_complete_p B p (j d)) hcU).choose_spec.1
  have hGF : G.comp F = RingHom.id H := by
    apply pdCompletionRingHom_ext B p (j d) H uB
      (pdCompletionH0_self_complete_p B p (j d)) (pdCompletionH0_self_complete_d B p (j d))
    · rw [RingHom.comp_assoc, hF]
      change G.comp ((uU).comp q) = uB
      rw [← RingHom.comp_assoc, hG, hkU]
    · rfl
  have hFG : F.comp G = RingHom.id HU := by
    apply pdCompletionRingHom_ext U p (jU d) HU uU
      (derivedDeltaDivision_complete_p D d a) (derivedDeltaDivision_complete_d D d a)
    · rw [RingHom.comp_assoc, hG]
      apply Ideal.Quotient.ringHom_ext
      change (F.comp kU).comp q = (uU).comp q
      rw [RingHom.comp_assoc, hkU, hF]
    · rfl
  exact RingEquiv.ofRingHom F G hFG hGF

/-- 概要：標準比較は元の raw 包の完備化像を旧ねじれ商の標準完備化像へ送る。
方針：順射の実完備化一意延長の合成仕様を評価する。
規約：全ての元の raw 包の元を扱う。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の係数を保つ比較。 -/
theorem rawDeltaDivisionPDTorsionEquiv_unit
    (hreg : let := pdCompletionCommRing B p (j d)
      Function.Injective (fun x : H => uB (j d) * x)) (r : B) :
    let := pdCompletionCommRing B p (j d)
    let := derivedDeltaDivisionCommRing D d a
    rawDeltaDivisionPDTorsionEquiv D d a hreg (uB r) = uU (q r) := by
  let := pdCompletionCommRing B p (j d)
  let := derivedDeltaDivisionCommRing D d a
  exact RingHom.congr_fun (existsUnique_pdCompletionRingHom B p (j d) HU ((uU).comp q)
    (derivedDeltaDivision_complete_p D d a) (derivedDeltaDivision_complete_d D d a)).choose_spec.1 r

/-- 概要：標準比較は実完備化の指定 δ 構造を保つ。
方針：raw 包からの標準合成が δ 射であることと実完備化の δ 延長性を使う。
規約：環同型の順射について述べる。
使われ方：BS 著者版 Proposition 7.2（著者版 p.55）、BS 著者版 Remark 7.15（p.62）の δ 完全化への比較。 -/
theorem rawDeltaDivisionPDTorsionEquiv_isDeltaHom
    (hreg : let := pdCompletionCommRing B p (j d)
      Function.Injective (fun x : H => uB (j d) * x)) :
    let := pdCompletionCommRing B p (j d)
    let := derivedDeltaDivisionCommRing D d a
    (DH).IsDeltaHom (derivedDeltaDivisionStructure D d a)
      (rawDeltaDivisionPDTorsionEquiv D d a hreg).toRingHom := by
  let := pdCompletionCommRing B p (j d)
  let := derivedDeltaDivisionCommRing D d a
  let K := RingHom.ker (algebraMap B (Localization.Away (j d)))
  have hq := (DB).isDeltaHom_quotient_mk ((DB).deltaClosure K) ((DB).isStable_deltaClosure K)
  have hk := (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D d a) (jU d)).comp hq
  apply pdCompletionRingHom_isDeltaHom DB (j d) (derivedDeltaDivisionStructure D d a)
    ((uU).comp q) hk (derivedDeltaDivision_complete_p D d a) (derivedDeltaDivision_complete_d D d a)
  apply RingHom.ext
  intro r
  exact rawDeltaDivisionPDTorsionEquiv_unit D d a hreg r

end SerrePositivity.BhattScholze.Andre

end RawDeltaDivisionPDTorsionComparison
