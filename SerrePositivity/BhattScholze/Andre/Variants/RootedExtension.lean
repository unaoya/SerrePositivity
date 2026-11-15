module

public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary
public import Mathlib.Algebra.Ring.TransferInstance
public import SerrePositivity.BhattScholze.Andre.Perfection.PerfectPrismMonic
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryFamily
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Family
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import SerrePositivity.BhattScholze.Andre.Envelope.PDivision
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import SerrePositivity.BhattScholze.Andre.Envelope.RootFamilyRaw
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedPerfection
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid

/-!
# 任意のモニック族の根付き perfectoid 拡大

## 概要
係数自己同型に沿う引戻し、完全 prism 商上・任意の整 perfectoid 基底上の任意モニック族の根付き拡大（`exists_monicRootedPerfectoidExtension`）、補助 raw φ/p 包の mod p 商・p 正則性・完全忠実平坦性・導来 p 剰余・δ 完全化の忠実平坦性、raw 包の完備化と完全 prism 候補の比較。
BS 著者版 Theorem 7.14 の証明に使う、モニック族に根を添加した perfectoid 拡大を構成する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/FrobeniusPullback`、`PowerRootEnvelope/PerfectionFaithful`、`Variants/MonicRootedExtension`。
-/

universe u v w

/-! ## 任意 raw δ 割り算包の実完備化先行完全化と既存完全 prism 候補

## 概要

任意の分子族について、元の raw 包を実完備化してから δ 完全化し再び実完備化する手順は、
既存の完全 prism 候補と標準係数射・生成元を保って環同型。
分母が distinguished なら生成元商も同型で整 perfectoid。
BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の構成比較。

## 方針

既存の実完備化・δ 完全化の順序交換同型と p 完備化先行比較を合成する。
冪根関係の比較 の根方程式に特化した比較を、方程式を使わない部分について一般化する。

## 規約

元の raw 包・実 H⁰ と標準射を使う。忠実平坦性の保存はこの比較だけから結論しない。

## 使われ方

無限根モニック実候補の完全 δ 化を、既存の perfectoid 候補へ接続する。
-/

@[expose] public noncomputable section RawDivisionPDPerfectionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "Raw" => DeltaAdjoinDivision D d a
local notation "F" => deltaAdjoinDivisionStructure D d a
local notation "ι" => deltaAdjoinDivisionMap D d a
local notation "z" => ι d
local notation "S" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v z)
local notation "H" => PDCompletionH0 C p x
local notation "s" => pdCompletionUnit C p x
local notation "rH" => RingHom.comp (RingHom.comp s (deltaPerfectionOf G 0)) v
local notation "rV" => RingHom.comp
  (pdCompletionUnit (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z))
  (pCompletedDeltaPerfectionMap F)

/-- 概要：任意 raw 包の実完備化先行完全化は既存の完全 prism 台環候補と環同型。
方針：二つの既存の順序比較を合成する。
規約：分子族・分母を任意とし、正則性を要求しない。
使われ方：BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の一般比較。 -/
def rawDivisionPDPerfectionEquiv :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    H ≃+* DivisionPrismCarrier D d a := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact (deltaPDCompletionPerfectionEquiv F z).symm.trans (deltaPerfectionPDCompletionEquiv F z)

/-- 概要：一般比較は元の raw 包からの標準射を保つ。
方針：二つの既存比較の raw 係数公式を順に使う。
規約：全ての raw 代表元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用の追跡。 -/
theorem rawDivisionPDPerfectionEquiv_comp_raw :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (rawDivisionPDPerfectionEquiv D d a).toRingHom.comp rH = rV := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  apply RingHom.ext
  intro b
  have h : (deltaPDCompletionPerfectionEquiv F z).symm (rH b) =
      pdCompletionUnit (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
        (deltaPerfectionOf F 0 b) :=
    RingHom.congr_fun (deltaPDCompletionPerfectionInverse_spec F z).2 b
  change deltaPerfectionPDCompletionEquiv F z
    ((deltaPDCompletionPerfectionEquiv F z).symm (rH b)) = rV b
  rw [h]
  exact RingHom.congr_fun (deltaPerfectionPDCompletionEquiv_spec F z).2.2 b

/-- 概要：一般比較の順逆両方向は指定 δ 構造を保つ。
方針：二つの順序比較の両方向の δ 性を合成する。
規約：完備化の既存 δ 構造を用いる。
使われ方：BS 著者版 Corollary 7.3（著者版 p.56）の完全 δ 化比較。 -/
theorem rawDivisionPDPerfectionEquiv_isDeltaHom :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (deltaPDCompletionStructure (deltaPerfectionStructure G) x).IsDeltaHom
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
        (pCompletedDeltaPerfectionMap F z)) (rawDivisionPDPerfectionEquiv D d a).toRingHom ∧
    (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
        (pCompletedDeltaPerfectionMap F z)).IsDeltaHom
      (deltaPDCompletionStructure (deltaPerfectionStructure G) x)
      (rawDivisionPDPerfectionEquiv D d a).symm.toRingHom := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact ⟨(deltaPerfectionPDCompletionEquiv_spec F z).1.comp
      (deltaPDCompletionPerfectionEquiv_spec F z).2.1,
    (deltaPDCompletionPerfectionEquiv_spec F z).1.comp
      (deltaPerfectionPDCompletionEquiv_spec F z).2.1⟩

/-- 概要：一般比較は指定分母の両候補での標準像を保つ。
方針：raw 係数公式を分母像で評価する。
規約：生成元を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商環比較。 -/
theorem rawDivisionPDPerfectionEquiv_generator :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    rawDivisionPDPerfectionEquiv D d a (s x) =
      pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a) p
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact RingHom.congr_fun (rawDivisionPDPerfectionEquiv_comp_raw D d a) z

/-- 概要：指定生成元商は既存の整 perfectoid 候補と環同型。
方針：生成元保存を主イデアル商へ降ろす。
規約：分母の distinguished 性のみを追加する。
使われ方：BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の perfectoid 商比較。 -/
def rawDivisionPDPerfectionQuotientEquiv (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (H ⧸ Ideal.span {s x}) ≃+* DivisionPerfectoidCandidate D d a hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact Ideal.quotientEquiv _ _ (rawDivisionPDPerfectionEquiv D d a) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(divisionPrism D d a hd).generator} =
      Ideal.span {rawDivisionPDPerfectionEquiv D d a (s x)}
    rw [rawDivisionPDPerfectionEquiv_generator]
    rfl)

/-- 概要：商比較は代表元に一般環同型を適用する。
方針：主イデアル商への降下の定義を使う。
規約：実 H⁰ の任意の元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数射と根の追跡。 -/
theorem rawDivisionPDPerfectionQuotientEquiv_mk (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    ∀ b : H, rawDivisionPDPerfectionQuotientEquiv D d a hd (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (rawDivisionPDPerfectionEquiv D d a b) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  dsimp only
  intro b
  rfl

/-- 概要：生成元商の比較も元の基底環からの自然係数射を保つ。
方針：raw 係数公式を主イデアル商射で送る。
規約：全ての元の係数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な根付き候補の比較。 -/
theorem rawDivisionPDPerfectionQuotientEquiv_comp_coefficient (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (rawDivisionPDPerfectionQuotientEquiv D d a hd).toRingHom.comp
      ((Ideal.Quotient.mk (Ideal.span {s x})).comp ((rH).comp ι)) =
      divisionPerfectoidCandidateMap D d a hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  apply RingHom.ext
  intro b
  change Ideal.Quotient.mk (divisionPrism D d a hd).ideal
    (rawDivisionPDPerfectionEquiv D d a (rH (ι b))) = _
  exact congrArg (Ideal.Quotient.mk (divisionPrism D d a hd).ideal)
    (RingHom.congr_fun (rawDivisionPDPerfectionEquiv_comp_raw D d a) (ι b))

/-- 概要：元の実完備化を δ 完全化し再完備化した標準生成元商は整 perfectoid。
方針：標準商環同型で既存の完全 prism 商の整 perfectoid 性を移す。
規約：忠実平坦性の保存を結論に含めない。
使われ方：BS 著者版 Corollary 7.3（著者版 p.56）、BS 著者版 Remark 7.15（p.62）の最終環候補。 -/
theorem rawDivisionPDPerfectionQuotient_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    IsIntegralPerfectoid (H ⧸ Ideal.span {s x}) p := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact isIntegralPerfectoid_of_ringEquiv p (rawDivisionPDPerfectionQuotientEquiv D d a hd).symm
    (divisionPerfectoidCandidate_isIntegralPerfectoid D d a hd)

end SerrePositivity.BhattScholze.Andre

end RawDivisionPDPerfectionComparison

/-! ## 係数環全体の自己同型に沿う実引戻し

## 概要

係数環 A の自己同型に関して半線形な環同型は、A 全体で取る通常テンソル引戻しの
代数同型を与える。BS 著者版 Remark 7.15(1)（著者版 p.62）の φ_A 引戻しを記述する。

## 方針

左の A を TensorBaseCopy A で区別し、既存の半線形テンソル同型を適用する。
原典とは異なる、実テンソルの普遍性を使う形式化上の経路。

## 規約

型の写しは宇宙を上げずに二つの係数作用を区別するために使う。
自己同型・二つの係数射・半線形性を全て明示し、商や正則性は仮定しない。

## 使われ方

実 Hodge–Tate ϖ 商の係数比較を、商環間だけでなく A 全体の Frobenius 引戻しに適用する。
-/

@[expose] public noncomputable section AutomorphismTensorPullback

namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct

/-- 概要：左係数環と元の係数環の作用を区別する同じ宇宙の型の写し。
方針：一つの値を持つ構造体として与える。
規約：元の環の情報を追加も削除もしない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の自己同型による引戻し。 -/
structure TensorBaseCopy (A : Type u) where
  value : A

/-- 概要：左係数環の写しは元の係数環と全単射。
方針：値を取り出す写像と一つの値を包む写像を逆とする。
規約：宇宙を変えない全単射。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実引戻しの環構造を定める。 -/
def tensorBaseCopyEquiv (A : Type u) : TensorBaseCopy A ≃ A where
  toFun := TensorBaseCopy.value
  invFun := TensorBaseCopy.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- 概要：係数環の写しには元の可換環構造を移す。
方針：値を取り出す全単射で環演算を移送する。
規約：自己同型によるスカラー作用はこの環構造と区別して後で指定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の通常テンソル。 -/
instance tensorBaseCopyCommRing {A : Type u} [CommRing A] : CommRing (TensorBaseCopy A) :=
  (tensorBaseCopyEquiv A).commRing

/-- 概要：係数環の写しと元の環は値を取り出す環同型で結ばれる。
方針：環構造を移した全単射を環同型へ強める。
規約：順方向は写しから元の A への射。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の左右の係数作用を明示する。 -/
def tensorBaseCopyRingEquiv (A : Type u) [CommRing A] : TensorBaseCopy A ≃+* A :=
  { tensorBaseCopyEquiv A with map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- 概要：自己同型に関して半線形な環同型は係数環全体の実引戻しを計算する。
方針：左係数環の写しとの同型を使い、通常テンソルの半線形比較を適用する。
規約：源と標的の自然な係数射を引数として固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の A 上の φ_A 引戻し。 -/
def automorphismTensorPullbackAlgEquiv (α : A ≃+* A) (q : A →+* B) (r : A →+* C)
    (F : B ≃+* C) (hF : ∀ a : A, F (q a) = r (α a)) :
    let := q.toAlgebra
    let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
    let := (α.trans (tensorBaseCopyRingEquiv A).symm).toRingHom.toAlgebra
    TensorBaseCopy A ⊗[A] B ≃ₐ[TensorBaseCopy A] C := by
  let := q.toAlgebra
  let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
  exact tensorBaseChangeAlgEquivOfSemilinearRingEquiv
    (α.trans (tensorBaseCopyRingEquiv A).symm) F (by
      intro a
      change F (q a) = r ((tensorBaseCopyRingEquiv A)
        ((tensorBaseCopyRingEquiv A).symm (α a)))
      rw [RingEquiv.apply_symm_apply]
      exact hF a)

/-- 概要：係数環全体の引戻し比較は単純テンソルを係数像と半線形像の積へ送る。
方針：既存の単純テンソル公式を係数環の写しへ特殊化する。
規約：左係数は写しの元を元の A に戻して評価する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の標準係数と根変数の追跡。 -/
theorem automorphismTensorPullbackAlgEquiv_tmul (α : A ≃+* A) (q : A →+* B)
    (r : A →+* C) (F : B ≃+* C) (hF : ∀ a : A, F (q a) = r (α a))
    (a : A) (b : B) :
    let := q.toAlgebra
    let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
    let := (α.trans (tensorBaseCopyRingEquiv A).symm).toRingHom.toAlgebra
    automorphismTensorPullbackAlgEquiv α q r F hF
      ((⟨a⟩ : TensorBaseCopy A) ⊗ₜ[A] b) = r a * F b := by
  let := q.toAlgebra
  let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
  rfl

end SerrePositivity.BhattScholze.Andre

end AutomorphismTensorPullback

/-! ## 完全 prism 商上の任意モニック族の根付き拡大

## 概要

完全 prism の商上の任意正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一段構成。

## 方針

同次数モニック lift を固定し、既存候補の標準基底射の完全忠実平坦性を適用する。
商の係数射で評価を移して、元の多項式族の根を得る。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる PD 先行構成と具体的比較による経路である。

## 規約

正次数を明示する。添字型全体に有限性を仮定しない。

## 使われ方

一般の perfectoid 基底への移送で、任意族の一段拡大を供給する。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicRootedExtension

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}
include hP

set_option maxHeartbeats 800000 in
-- 同じ候補の完備化台環と標準係数作用を含む存在証人の定義展開に必要。
/-- 概要：完全 prism 商上の任意正次数モニック族の全根を同じ p 完全忠実平坦拡大に得る。
方針：同次数モニック lift に候補の平坦性を適用し、評価の自然性で根を降ろす。
規約：添字型は任意で、補助的な平坦性仮定を要求しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の別証明の一段構成。 -/
theorem exists_monicRootedPerfectoidExtension_of_perfectPrism
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let F := perfectPrismMonicLift P f hf
  have hF : ∀ s, (F s).Monic := fun s => (perfectPrismMonicLift_spec P f hf s).2
  have hFdeg : ∀ s, 0 < (F s).natDegree := by
    intro s
    rw [(perfectPrismMonicLift_spec P f hf s).1]
    exact hdeg s
  let D := P.deltaStructure
  let d := P.generator
  let hd := OrientedPrism.isDistinguished_generator P
  let := polynomialPrismCommRing D d F
  let φ := polynomialPerfectoidCandidateBaseMap D d F hd
  let ρ := polynomialPerfectoidCandidateRoot D d F hd
  refine ⟨PolynomialPerfectoidCandidate D d F hd, inferInstance, φ, ρ,
    polynomialPerfectoidCandidate_isIntegralPerfectoid D d F hd,
    perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat_arbitrary P hP F hF hFdeg, ?_⟩
  intro s
  rw [← perfectPrismMonicLift_map P f hf s, Polynomial.eval₂_map]
  exact polynomialPerfectoidCandidate_eval D d F hd s

end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicRootedExtension

/-! ## 先行関係の冪と係数商の後のモニック正則性

## 概要

mod p と先行する独立多項式関係の p 乗で割った後も、残りの変数のモニック関係は
非零因子である。BS 著者版 Corollary 2.39（p.25）の独立関係族への計算に使う。

## 方針

係数商と多項式環の交換同型を実関係イデアルの商まで降ろす。
多項式評価と冪が可換することから、冪の先行商を任意多項式族の先行商として扱う。

## 規約

p の素数性、先行族のモニック性や有限性はこの正則性には不要。
後続多項式だけモニックとする。prismatic envelope の忠実平坦性は別工程。

## 使われ方

一般モニック族の raw δ p 除算包に一入力を追加する帰納の正則性入力を供給する。
-/

@[expose] public noncomputable section MonicFamilyPowerResidue

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}
variable (I : Ideal R) (T : Set σ) (f : σ → Polynomial R)

local notation "IB" => I.map (MvPolynomial.C : R →+* MvPolynomial σ R)
local notation "J" => polynomialSubsetRelationIdeal T f
local notation "Jbar" => polynomialSubsetRelationIdeal T
  (fun s => Polynomial.map (Ideal.Quotient.mk I) (f s))

/-- 概要：係数商は先行関係イデアルを係数変更された先行関係イデアルへ送る。
方針：係数商の可換公式と評価の係数変更公式を各生成元に適用する。
規約：任意係数イデアルと任意先行族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の残余表示の係数を固定する。 -/
theorem polynomialSubsetIdeal_map_coefficientQuotient :
    ((J).map (Ideal.Quotient.mk IB)).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom = Jbar := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [polynomialSubsetRelationIdeal, Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  exact monicRelation_map _ _ _

/-- 概要：係数イデアルと先行関係を同時に課す商は、係数変更後の先行関係商に同型。
方針：二重商と係数商の交換同型を合成する。
規約：実商射を保つ同型を選ぶ。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の mod p 正則性に適用する。 -/
def polynomialSubsetBaseQuotientEquiv :
    (MvPolynomial σ R ⧸ (IB ⊔ J)) ≃+* (MvPolynomial σ (R ⧸ I) ⧸ Jbar) :=
  (DoubleQuot.quotQuotEquivQuotSup IB J).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (polynomialSubsetIdeal_map_coefficientQuotient I T f).symm)

/-- 概要：同時商の同型は各代表元の係数をそのまま商へ写す。
方針：二重商と係数商の代表元公式を使う。
規約：関係式の標準像についての計算に用いる。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実残余入力を同定する。 -/
theorem polynomialSubsetBaseQuotientEquiv_mk (x : MvPolynomial σ R) :
    polynomialSubsetBaseQuotientEquiv I T f (Ideal.Quotient.mk (IB ⊔ J) x) =
      Ideal.Quotient.mk Jbar (MvPolynomial.map (Ideal.Quotient.mk I) x) := by
  change Ideal.Quotient.mk Jbar
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk IB x)) = _
  congr 1
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ R I) x

/-- 概要：係数商と先行関係の商の後でも、残りのモニック関係は非零因子。
方針：同時商を係数変更後の商へ移して、先行族商の正則性を適用する。
規約：先行多項式と後続多項式を独立に取る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の独立関係族の正則性入力。 -/
theorem polynomialSubsetBaseQuotient_remaining_isSMulRegular
    (h : Polynomial R) (hh : h.Monic) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ R ⧸ (IB ⊔ J))
      (Ideal.Quotient.mk (IB ⊔ J) (monicRelation h s)) := by
  let e := polynomialSubsetBaseQuotientEquiv I T f
  have he : e (Ideal.Quotient.mk _ (monicRelation h s)) =
      Ideal.Quotient.mk Jbar (monicRelation (h.map (Ideal.Quotient.mk I)) s) := by
    rw [polynomialSubsetBaseQuotientEquiv_mk, monicRelation_map]
  have hr := polynomialSubsetQuotient_remaining_isSMulRegular T
    (fun t => (f t).map (Ideal.Quotient.mk I))
    (h.map (Ideal.Quotient.mk I)) (hh.map (Ideal.Quotient.mk I)) s hs
  intro x y hxy
  apply e.injective
  apply hr
  have heq := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using heq

omit I in
/-- 概要：実 mod p と先行関係の p 乗商の後も残りのモニック関係は非零因子。
方針：先行する冪関係を元の多項式の冪の評価に書き換え、係数商版を適用する。
規約：p の素数性も先行関係の正則性も不要。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の raw δ p 除算の有限族帰納に使う。 -/
theorem polynomialSubsetPowerModP_remaining_isSMulRegular
    (p : ℕ) (h : Polynomial R) (hh : h.Monic) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ R ⧸ (Ideal.span {(p : MvPolynomial σ R)} ⊔
      Ideal.span (Set.range fun t : T => monicRelation (f t) (t : σ) ^ p)))
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial σ R)} ⊔
        Ideal.span (Set.range fun t : T => monicRelation (f t) (t : σ) ^ p))
          (monicRelation h s)) := by
  have hr := polynomialSubsetBaseQuotient_remaining_isSMulRegular
    (Ideal.span {(p : R)}) T (fun s => (f s) ^ p) h hh s hs
  have hI : (Ideal.span {(p : R)}).map (MvPolynomial.C : R →+* MvPolynomial σ R) =
      Ideal.span {(p : MvPolynomial σ R)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, map_natCast]
  rw [hI] at hr
  have hJ : polynomialSubsetRelationIdeal T (fun s => (f s) ^ p) =
      Ideal.span (Set.range fun t : T => monicRelation (f t) (t : σ) ^ p) := by
    unfold polynomialSubsetRelationIdeal
    congr 1
    congr 1
    funext t
    exact Polynomial.eval₂_pow _ _ p
  rw [hJ] at hr
  exact hr

end SerrePositivity.BhattScholze.Andre

end MonicFamilyPowerResidue

/-! ## André：一元モニック関係の raw δ p 除算包の p 正則性

## 概要

モニック多項式を独立変数で評価した y に対し、raw δ 環の `φ(y)/p` 添加で
p は非零因子となる。BS 著者版 Corollary 2.39（p.25）の一元入力に対応する。

## 方針

モニック性から mod p 正則性を供給し、既存の任意正則元の raw p 除算定理を適用する。
ghost 単射は係数環の p 正則性から多項式環の自由性と ghost 成分の単射性の補題 により供給する。

## 規約

これは補助的な `φ(y)/p` 計算であり、一般 d による `y/d` 包そのものの平坦性ではない。
正次数はこの p 正則性には不要。prismatic envelope の比較は別工程。

## 使われ方

BS 著者版 Remark 7.15（著者版 p.62）の pd 計算と δ 除算の比較への正則入力。
-/

@[expose] public noncomputable section MonicRawPDivision

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A τ : Type u} [CommRing A]

local notation "B" => MvPolynomial τ A

/-- 概要：p 正則な δ 係数環と単元 δ(p) の下で、一元モニック関係の raw p 除算包は p 正則。
方針：mod p のモニック正則性を既存 raw 包定理へ渡し、ghost 単射を内部で供給する。
規約：モニック f の正次数は不要である。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の補助 p 除算計算。 -/
theorem monicRawPDivision_p_mul_injective
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : τ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) :
    Function.Injective (fun x : DeltaAdjoinDivision (polynomialRankOneDeltaStructure τ D)
      (p : B) (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ D).frobeniusLift
        (monicRelation f s)) =>
      (p : DeltaAdjoinDivision (polynomialRankOneDeltaStructure τ D)
        (p : B) (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ D).frobeniusLift
          (monicRelation f s))) * x) := by
  let E := polynomialRankOneDeltaStructure τ D
  let L := RelativeFreeDeltaRing (R := B) PUnit.{u + 1}
  have hpB : Function.Injective (fun x : B => (p : B) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := B)
  have hg : Function.Injective (WittVector.ghostMap : WittVector p L → ℕ → L) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular B (p : B) from hpB).of_flat (S := L)
  obtain ⟨v, hv⟩ := hdp
  let w := Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* B)) v
  have hw : (w : B) = E.delta (p : B) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, ← polynomialRankOneDeltaStructure_delta_C τ D (p : A), map_natCast]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionRaw_p_mul_injective (σ := PUnit.{u + 1}) E (monicRelation f s)
    hpB hg w hw (monicRelation_modP_isSMulRegular p f hf s)

/-- 概要：完全 prism 上では一元モニック関係の raw φ/p 包は p 正則。
方針：完全 δ 構造の p 正則性と p 完備性から前定理の入力を供給する。
規約：prism の商の p ねじれなしは主張しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の補助 p 除算計算の具体的入力。 -/
theorem perfectPrismMonicRawPDivision_p_mul_injective
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : τ) :
    Function.Injective (fun x : DeltaAdjoinDivision
      (polynomialRankOneDeltaStructure τ P.deltaStructure) (p : B)
      (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ P.deltaStructure).frobeniusLift
        (monicRelation f s)) =>
      (p : DeltaAdjoinDivision (polynomialRankOneDeltaStructure τ P.deltaStructure) (p : B)
        (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ P.deltaStructure).frobeniusLift
          (monicRelation f s))) * x) := by
  let := P.isAdicComplete_p_of_perfect hP
  apply monicRawPDivision_p_mul_injective P.deltaStructure f hf s hP.p_mul_injective
  exact DeltaStructure.isDistinguished_p P.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

end SerrePositivity.BhattScholze.Andre

end MonicRawPDivision

/-! ## 任意モニック族の raw δ p 除算包の p 正則性

## 概要

p 正則な δ 係数環上の独立変数ごとの任意モニック関係族について、各関係の
Frobenius 像を同時に p で除算した raw 環で p は非零因子となる。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の補助計算に対応する。

## 方針

有限先行族の関係の p 乗商での正則性により一入力追加の帰納を行う。
ghost 単射を p 正則性から内部で供給し、有限部分族の既存余極限で任意族へ移す。

## 規約

δ(p) は単元と仮定する。正次数は不要で、係数環や族の有限性も要求しない。
これは補助 φ/p 包の p 正則性であり、f/d 包やその perfectoid 商の忠実平坦性ではない。

## 使われ方

任意モニック関係族に対する pd 比較と実導来 p 完備化の入力に用いる。
-/

@[expose] public noncomputable section MonicFamilyRawRegular

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime]

/-- 概要：p 正則な係数環上の相対自由 δ 源では ghost 射が単射。
方針：多項式環の自由性で p 正則性を移し ghost 成分の単射性の補題 を適用する。
規約：添字の有限性は不要。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の有限族帰納の ghost 入力。 -/
private theorem sourceGhost_injective {S : Type u} [CommRing S]
    (hpS : Function.Injective (fun x : S => (p : S) * x)) (ι : Type v) :
    Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := S) ι) → ℕ → RelativeFreeDeltaRing (R := S) ι) := by
  apply witt_ghostMap_injective_of_mul_prime_injective
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular S (p : S) from hpS).of_flat
      (S := RelativeFreeDeltaRing (R := S) ι)

variable {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => fun s : σ => monicRelation (f s) s

/-- 概要：任意有限部分族のモニック関係の raw φ/p 包は p 正則。
方針：先行 p 乗商の後続正則性で一入力追加を帰納し、ghost 単射を ghost 成分の単射性の補題 から供給する。
規約：モニック関係の次数は正でなくてもよい。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の有限独立関係族の raw 計算。 -/
theorem monicFiniteRaw_p_mul_injective (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) (T : Finset σ) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P)
      (fun s : T => DeltaStructure.frobeniusLift E (r s)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun s : T => DeltaStructure.frobeniusLift E (r s))) * x) := by
  classical
  have hpP : Function.Injective (fun x : P => (p : P) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  obtain ⟨w, hw⟩ := hdp
  let wP := Units.map (MvPolynomial.C : A →+* P).toMonoidHom w
  have hwP : (wP : P) = DeltaStructure.delta E (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  induction T using Finset.induction_on with
  | empty =>
    let e := deltaAdjoinDivisionEmptyEquiv E (p : P)
      (fun s : (∅ : Finset σ) => DeltaStructure.frobeniusLift E (r s))
    intro x y hxy
    apply e.injective
    apply hpP
    simpa only [map_mul, map_natCast] using congrArg e hxy
  | @insert s T hs ih =>
    have hx : IsSMulRegular
        (P ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T => r t ^ p))
        (Ideal.Quotient.mk
          (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T => r t ^ p)) (r s)) := by
      have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
        congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal, hpp]
      exact polynomialSubsetPowerModP_remaining_isSMulRegular (T : Set σ) f p (f s) (hf s) s hs
    have hstep := _root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionFamilySum_p_mul_injective (η := PUnit.{max u v + 1}) E
      (fun t : T => r t) (r s) hpP ih (sourceGhost_injective hpP T)
      (sourceGhost_injective ih PUnit.{max u v + 1}) wP hwP hx
    let ρ := _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteInsertIndexEquiv (η := PUnit.{max u v + 1}) T s hs
    let e := deltaAdjoinDivisionReindexEquiv E (p : P)
      (Sum.elim (fun t : T => DeltaStructure.frobeniusLift E (r t))
        (fun _ : PUnit.{max u v + 1} => DeltaStructure.frobeniusLift E (r s)))
      (fun t : (insert s T : Finset σ) => DeltaStructure.frobeniusLift E (r t)) ρ
      (fun t => by cases t <;> rfl)
    intro x y hxy
    apply e.symm.injective
    apply hstep
    simpa only [map_mul, map_natCast] using congrArg e.symm hxy

/-- 概要：任意個の独立モニック関係の raw φ/p 包は p 正則。
方針：すべての有限部分族の p 正則性を既存の有限部分族余極限で移す。
規約：族の濃度に制限を置かず、遷移射の単射性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の任意根族への補助 raw 計算。 -/
theorem monicFamilyRaw_p_mul_injective (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P)
      (fun s : σ => DeltaStructure.frobeniusLift E (r s)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun s : σ => DeltaStructure.frobeniusLift E (r s))) * x) := by
  apply deltaAdjoinDivisionFamily_p_mul_injective E (p : P)
    (fun s : σ => DeltaStructure.frobeniusLift E (r s))
  intro T
  exact monicFiniteRaw_p_mul_injective D f hf hpA hdp T

/-- 概要：完全 prism 上の任意モニック族の補助 raw φ/p 包は p 正則。
方針：完全 δ 構造から係数環の p 正則性と p 完備性を取り出し、任意族版に適用する。
規約：prism の商の p 正則性や最終候補の忠実平坦性は結論しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 比較の raw 正則性入力。 -/
theorem perfectPrismMonicFamilyRaw_p_mul_injective
    (P₀ : OrientedPrism p A) (hP : P₀.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ s, (f s).Monic) :
    Function.Injective (fun x : DeltaAdjoinDivision
      (polynomialRankOneDeltaStructure σ P₀.deltaStructure) (p : MvPolynomial σ A)
      (fun s : σ => (polynomialRankOneDeltaStructure σ P₀.deltaStructure).frobeniusLift
        (monicRelation (f s) s)) =>
      (p : DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ P₀.deltaStructure)
        (p : MvPolynomial σ A)
        (fun s : σ => (polynomialRankOneDeltaStructure σ P₀.deltaStructure).frobeniusLift
          (monicRelation (f s) s))) * x) := by
  let := P₀.isAdicComplete_p_of_perfect hP
  apply monicFamilyRaw_p_mul_injective P₀.deltaStructure f hf hP.p_mul_injective
  exact DeltaStructure.isDistinguished_p P₀.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

end SerrePositivity.BhattScholze.Andre

end MonicFamilyRawRegular

/-! ## モニック族の raw φ/p 包の実 mod p 商の忠実平坦性

## 概要

正次数モニック族の raw 同時 φ/p 包の実 p 商は、元の係数環 A/p 上忠実平坦。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の実剰余計算に対応する。

## 方針

一般 δ 除算の raw 剰余の、初期係数商上の忠実平坦性を再利用する。
前工程の初期係数商の A/p 忠実平坦性と合成し、raw (p,p) 剰余を実 p 商と同定する。

## 規約

このファイルでは係数環の p 正則性、相対自由源の ghost 単射と単元 δ(p) を明示する。
次工程でこれらを証明から供給する。完備化後の平坦性は別工程。

## 使われ方

実剰余テンソルの忠実平坦性と p 完全忠実平坦性の判定に使う。
-/

@[expose] public noncomputable section MonicRawModPFlat

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "Q" => MonicFrobeniusCoefficientQuotient D f
local notation "Res" => DeltaAdjoinDivisionResidue E (p : P) a
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "wp" => Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* P)) w

/-- 概要：raw (p,p) 剰余への元の A/p からの実係数射。
方針：初期係数商の標準係数射と一般 raw 剰余の係数射を合成する。
規約：源の p 正則性と ghost 単射を明示して一般定理を使用する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実係数作用を固定する。 -/
def monicRawResidueBaseMap : QA →+* Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P => (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L => (p : L) * x) := hL
  have hwp : (wp : P) = DeltaStructure.delta E (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  exact (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg (p : P) a wp hwp).comp
    (monicFrobeniusCoefficientBaseMap D f)

/-- 概要：raw 剰余の A/p 係数射は元の A の係数の標準剰余像に一致する。
方針：二つの係数射の代表元公式を合成する。
規約：任意の元の A 係数について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数射を保つ。 -/
theorem monicRawResidueBaseMap_mk (x : A) :
    monicRawResidueBaseMap D f hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [monicRawResidueBaseMap, RingHom.comp_apply, monicFrobeniusCoefficientBaseMap_mk,
    deltaAdjoinDivisionResidueBaseMap_mk]

/-- 概要：raw 剰余の標準 A/p 代数構造。
方針：明示した係数射の toAlgebra を取る。
規約：利用時に局所導入する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の raw 剰余の平坦性。 -/
@[instance_reducible] def monicRawResidueBaseAlgebra : Algebra QA Res :=
  (monicRawResidueBaseMap D f hpA hg w hw).toAlgebra

/-- 概要：正次数モニック族の raw (p,p) 剰余は元の A/p 上忠実平坦。
方針：初期係数商と raw 剰余の二つの忠実平坦性を標準係数射で合成する。
規約：族の有限性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実剰余の忠実平坦性。 -/
theorem monicRawResidue_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicRawResidueBaseAlgebra D f hpA hg w hw
    Module.FaithfullyFlat QA Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P => (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L => (p : L) * x) := hL
  have hwp : (wp : P) = DeltaStructure.delta E (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  let := monicFrobeniusCoefficientBaseAlgebra D f
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL hg (p : P) a wp hwp
  let := monicRawResidueBaseAlgebra D f hpA hg w hw
  let : IsScalarTower QA Q Res := IsScalarTower.of_algebraMap_eq' rfl
  let := monicFrobeniusCoefficient_faithfullyFlat D f hf hdeg
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP hpL hg (p : P) a wp hwp
  exact Module.FaithfullyFlat.trans QA Q Res

/-- 概要：実 raw p 商への元の A/p 係数射。
方針：raw (p,p) 剰余と実 p 商の既存同型の逆を合成する。
規約：同じ係数作用を実 p 商上に置く。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実 mod p 加群。 -/
def monicRawModPBaseMap : QA →+* (B ⧸ Ideal.span {(p : B)}) :=
  (deltaAdjoinDivisionPQuotientResidueEquiv E a).symm.toRingHom.comp
    (monicRawResidueBaseMap D f hpA hg w hw)

/-- 概要：実 p 商への係数射は標準 raw 係数射の剰余と一致する。
方針：剰余同型を適用して前の代表元公式に帰着する。
規約：元の A からの標準係数像を追跡する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余テンソルとの比較。 -/
theorem monicRawModPBaseMap_mk (x : A) :
    monicRawModPBaseMap D f hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [monicRawModPBaseMap, RingHom.comp_apply]
  apply (deltaAdjoinDivisionPQuotientResidueEquiv E a).injective
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    ((deltaAdjoinDivisionPQuotientResidueEquiv E a).symm _) = _
  rw [RingEquiv.apply_symm_apply, monicRawResidueBaseMap_mk,
    deltaAdjoinDivisionPQuotientResidueEquiv_mk]

/-- 概要：実 raw p 商の標準 A/p 代数構造。
方針：実 p 商への標準係数射の toAlgebra を使う。
規約：元の A/p の作用を変えない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実 mod p 忠実平坦性。 -/
@[instance_reducible] def monicRawModPBaseAlgebra :
    Algebra QA (B ⧸ Ideal.span {(p : B)}) :=
  (monicRawModPBaseMap D f hpA hg w hw).toAlgebra

/-- 概要：raw (p,p) 剰余との比較は標準 A/p 作用を保つ代数同型。
方針：逆射で定義した係数射の可換性を確認する。
規約：通常の環同型だけでなく A/p 線形性を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の忠実平坦性を実 p 商へ移す。 -/
def monicRawModPResidueAlgEquiv :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    letI := monicRawResidueBaseAlgebra D f hpA hg w hw
    (B ⧸ Ideal.span {(p : B)}) ≃ₐ[QA] Res := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  let := monicRawResidueBaseAlgebra D f hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := deltaAdjoinDivisionPQuotientResidueEquiv E a)
  intro x
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    (monicRawModPBaseMap D f hpA hg w hw x) = monicRawResidueBaseMap D f hpA hg w hw x
  rw [monicRawModPBaseMap, RingHom.comp_apply]
  exact (deltaAdjoinDivisionPQuotientResidueEquiv E a).apply_symm_apply _

/-- 概要：任意の正次数モニック族の raw φ/p 包の実 p 商は A/p 上忠実平坦。
方針：raw 剰余との代数同型で証明済みの剰余忠実平坦性を移す。
規約：係数射と族の正次数を明示し、完備化はまだ行わない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の p 完全忠実平坦性の剰余入力。 -/
theorem monicRawModP_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    Module.FaithfullyFlat QA (B ⧸ Ideal.span {(p : B)}) := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  let := monicRawResidueBaseAlgebra D f hpA hg w hw
  let := monicRawResidue_faithfullyFlat D f hpA hg w hw hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv QA Res
    (monicRawModPResidueAlgEquiv D f hpA hg w hw).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end MonicRawModPFlat

/-! ## 任意モニック族の補助 raw φ/p 包の p 完全忠実平坦性

## 概要

p 正則な δ 係数環上で δ(p) が単元なら、正次数モニック族の補助 raw φ/p 包は
元の係数射に関して p 完全忠実平坦。BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15（p.62）の準備。

## 方針

実 p 商の忠実平坦性を元の A→A/p に沿う通常テンソルの忠実平坦性へ移す。
前工程の raw p 正則性と主元の完全忠実平坦性判定を組み合わせる。

## 規約

これは補助 φ(f)/p 包の結果であり、f/d 包やその perfectoid 商の平坦性ではない。
族の有限性や ghost 単射を追加仮定にしない。p 正則性は基底 prism の台環に要求する。

## 使われ方

prismatic envelope の比較で必要となる補助 pd 計算の p 完全忠実平坦性を供給する。
-/

@[expose] public noncomputable section MonicRawCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity.BhattScholze.Andre

open scoped _root_.TensorProduct

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I

/-- 概要：元の δ 係数環から補助 raw 包への実係数射。
方針：多項式係数包含と raw δ 添加の係数射を合成する。
規約：標準の A 代数作用と同じ射を用いる。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の元の係数作用を明示する。 -/
def monicRawCoefficientMap : A →+* B :=
  (deltaAdjoinDivisionMap E (p : P) a).comp MvPolynomial.C

/-- 概要：raw 包の標準代数構造の係数射は明示した実係数射と一致する。
方針：定義の一致による。
規約：係数作用を別の代数構造に取り替えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余テンソルの係数比較。 -/
theorem monicRawCoefficient_algebraMap : algebraMap A B = monicRawCoefficientMap D f := rfl

/-- 概要：基底の p イデアルの raw 包への拡張は raw 包自身の p イデアル。
方針：環射の自然数係数の保存を使う。
規約：元の A 係数射に沿う拡張。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の通常 mod p 基底変更を同定する。 -/
theorem monicRawCoefficient_map_span_p :
    (I).map (algebraMap A B) = Ideal.span {(p : B)} := by
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))

/-- 概要：基底の p イデアルの拡張による商と実 raw p 商の比較は A/p 代数同型。
方針：拡張イデアルの等式と、係数の代表元公式を使う。
規約：実 p 商には前工程の明示的な A/p 作用を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数剰余作用を保持する。 -/
def monicRawCoefficientQuotientAlgEquiv :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    (B ⧸ (I).map (algebraMap A B)) ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (monicRawCoefficient_map_span_p D f))
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq (monicRawCoefficient_map_span_p D f)
    (Ideal.Quotient.mk _ (monicRawCoefficientMap D f x)) =
      monicRawModPBaseMap D f hpA hg w hw (Ideal.Quotient.mk I x)
  rw [Ideal.quotEquivOfEq_mk, monicRawModPBaseMap_mk]
  rfl

/-- 概要：元の A→A/p に沿う通常基底変更は実 raw p 商に A/p 代数同型。
方針：商テンソル比較と実 p 商の係数作用の同型を合成する。
規約：元の標準 A 代数作用を固定する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の主元平坦性判定の剰余テンソル。 -/
def monicRawBaseChangeModPAlgEquiv :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    QA ⊗[A] B ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.trans
    (monicRawCoefficientQuotientAlgEquiv D f hpA hg w hw)

include hpA w hw in
omit hg in
/-- 概要：正次数モニック族の raw 包の通常剰余テンソルは A/p 上忠実平坦。
方針：ghost 成分の単射性の補題 で ghost 単射を供給し、実 p 商との代数同型で忠実平坦性を移す。
規約：族の濃度に制限せず、外部 ghost 仮定を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p 完全忠実平坦性の剰余入力。 -/
theorem monicRaw_residueTensor_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat QA (QA ⊗[A] B) := by
  let hg := _root_.SerrePositivity.BhattScholze.Andre.deltaRootSource_ghostMap_injective (σ := σ) hpA
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  let := monicRawModP_faithfullyFlat D f hpA hg w hw hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (monicRawBaseChangeModPAlgEquiv D f hpA hg w hw).toLinearEquiv

include hpA in
omit hg w hw in
/-- 概要：raw 包の p 正則性を元の係数スカラー作用について表す。
方針：任意モニック族の raw p 正則性と自然数係数の保存を使う。
規約：モニック性は使うが正次数は不要。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の主元平坦性判定の Tor 消滅入力。 -/
theorem monicRaw_p_smul_regular (hf : ∀ s, (f s).Monic)
    (hdp : D.IsDistinguished (p : A)) : IsSMulRegular B (p : A) := by
  intro x y hxy
  apply monicFamilyRaw_p_mul_injective D f hf hpA hdp
  simpa only [Algebra.smul_def, map_natCast] using hxy

include hpA in
omit hg w hw in
/-- 概要：任意正次数モニック族の補助 raw φ/p 包は元の係数射で p 完全忠実平坦。
方針：係数と raw 包の p 正則性、実剰余テンソルの忠実平坦性を主元の判定へ渡す。
規約：δ(p) の単元性を明示し、完備化後の主張と区別する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一般 prism 包との比較への補助入力。 -/
theorem monicFamilyRaw_isCompletelyFaithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree)
    (hdp : D.IsDistinguished (p : A)) : IsCompletelyFaithfullyFlat I B := by
  have hB := monicRaw_p_smul_regular D f hpA hf hdp
  obtain ⟨w, hw⟩ := hdp
  exact isCompletelyFaithfullyFlat_principal_of_regular (p : A) hpA B hB
    (monicRaw_residueTensor_faithfullyFlat D f hpA w hw hf hdeg)

omit D hpA hg w hw in
/-- 概要：完全 prism 上の任意正次数モニック族の補助 raw φ/p 包は p 完全忠実平坦。
方針：完全 δ 構造の p 正則性と p 完備性から前定理の入力を内部で供給する。
規約：最終 f/d 包やその perfectoid 商の忠実平坦性はまだ主張しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全 prism の補助 pd 計算。 -/
theorem perfectPrismMonicFamilyRaw_isCompletelyFaithfullyFlat
    (P₀ : OrientedPrism p A) (hP : P₀.deltaStructure.IsPerfect)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)})
      (DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ P₀.deltaStructure)
        (p : MvPolynomial σ A)
        (fun s : σ => DeltaStructure.frobeniusLift
          (polynomialRankOneDeltaStructure σ P₀.deltaStructure) (monicRelation (f s) s))) := by
  let := P₀.isAdicComplete_p_of_perfect hP
  apply monicFamilyRaw_isCompletelyFaithfullyFlat P₀.deltaStructure f hP.p_mul_injective hf hdeg
  exact DeltaStructure.isDistinguished_p P₀.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

end SerrePositivity.BhattScholze.Andre

end MonicRawCompletelyFlat

/-! ## 補助 raw 包の実導来 p 剰余

## 概要

任意正次数モニック族の補助 φ(f)/p 包は、実導来 mod p 還元の非零次数が消え、
H⁰ が A/p 上忠実平坦である。BS 著者版 Corollary 2.39（著者版 p.25）、BS 著者版 Remark 7.15（p.62）の準備。

## 方針

元の係数射の p 正則性から標準 augmentation を同型にし、実 H⁰ 比較で通常忠実平坦性を移す。

## 規約

対象は補助 raw 包の single の実導来還元である。一般 f/d 包との比較は主張しない。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の補助計算。

## 使われ方

既存の一般 δ 完全化の剰余比較へ、明示した元の係数射に関する入力を渡す。
-/

@[expose] public noncomputable section MonicRawDerivedReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "j" => monicRawCoefficientMap D f
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "M" => baseChangeScalarModule j
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hf : ∀ s, (f s).Monic) (hdp : D.IsDistinguished (p : A))
include hpA hf hdp

/-- 概要：元の係数射の制限加群で p は正則。
方針：raw 包の標準 p 作用の正則性を係数射の定義で移す。
規約：モニック性と係数環の p 正則性、δ(p) の単元性を用いる。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実導来剰余の Tor 入力。 -/
theorem monicRaw_scalarModule_p_regular : IsSMulRegular M (p : A) := by
  intro x y h
  change B at x y
  apply monicFamilyRaw_p_mul_injective D f hf hpA hdp
  change j (p : A) * x = j (p : A) * y at h
  simpa only [map_natCast] using h

/-- 概要：補助 raw 包の元の係数射は、p 商に沿う高次 Tor が消える。
方針：係数環と制限加群の p 正則性に主元 Tor 判定を適用する。
規約：実係数加群を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実導来 mod p 還元を離散化する。 -/
theorem monicRaw_scalarExtensionTorVanishing : scalarExtensionTorVanishing q M :=
  scalarExtensionTorVanishing_principal_of_regular (p : A) hpA M
    (monicRaw_scalarModule_p_regular D f hpA hf hdp)

/-- 概要：raw 包の実導来 mod p 還元は通常剰余の single と標準同型。
方針：前定理を標準 augmentation の同型判定に渡す。
規約：導来対象の抽象的な置き換えではなく既存 augmentation を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次数零比較への準備。 -/
def monicRaw_modPAugmentationIso :
    Y ≅ boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q).obj M) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (monicRaw_scalarExtensionTorVanishing D f hpA hf hdp)

/-- 概要：補助 raw 包の実導来 mod p 還元の非零次数ホモロジーは零。
方針：標準 augmentation 同型から single のホモロジー消滅を移す。
規約：全非零整数次数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 完全化の実剰余入力。 -/
theorem monicRaw_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat QA) i).obj (Y).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat QA) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (monicRaw_modPAugmentationIso D f hpA hf hdp))
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso e

omit hpA hf hdp in
/-- 概要：制限加群の通常 p 剰余と、標準 raw 係数作用の通常テンソルは A/p 線形同型。
方針：商スカラー拡大と商テンソルの二つの標準比較を合成する。
規約：係数射の定義による同じ A 作用を使う。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の忠実平坦性を実 H⁰ に移す。 -/
def monicRaw_scalarResidueTensorEquiv :
    ((ModuleCat.extendScalars q).obj M) ≃ₗ[QA] QA ⊗[A] B := by
  let e : M ≃ₗ[A] B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c x
        change B at x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def]
        change j c * x = algebraMap A B c * x
        rw [monicRawCoefficient_algebraMap] }
  exact (quotientScalarExtensionEquiv I M).trans
    (((quotientModuleFunctor I).mapIso e.toModuleIso).toLinearEquiv.trans
      (quotientTensorReductionEquiv I B).symm)

/-- 概要：補助 raw 包の実導来 mod p 還元の H⁰ は A/p 上忠実平坦。
方針：通常剰余テンソルの忠実平坦性を実 H⁰ の標準線形同型で移す。
規約：任意濃度の正次数モニック族。ghost 単射仮定は内部で解消する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一般 δ 完全化の剰余入力。 -/
theorem monicRaw_modPH0_faithfullyFlat (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat QA
      ((DerivedCategory.homologyFunctor (ModuleCat QA) 0).obj (Y).obj) := by
  obtain ⟨w, hw⟩ := hdp
  have := monicRaw_residueTensor_faithfullyFlat D f hpA w hw hf hdeg
  let e := ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv |>.trans
    (monicRaw_scalarResidueTensorEquiv D f)
  exact Module.FaithfullyFlat.of_linearEquiv QA (QA ⊗[A] B) e

end SerrePositivity.BhattScholze.Andre

end MonicRawDerivedReduction

/-! ## 補助 raw 包の δ 完全化の忠実平坦剰余

## 概要

完全 δ 係数環上で、正次数モニック族の補助 φ(f)/p 包の δ 完全化は p 完全忠実平坦。
BS 著者版 Corollary 2.39（著者版 p.25）、BS 著者版 Remark 7.15（p.62）の準備。

## 方針

実 raw 包の導来 mod p 入力を、既存の一般 δ 完全化の剰余忠実平坦性に渡す。
完全化の p 正則性と主元判定を接続する。原典の BS 著者版 Proposition 7.11 とは異なる経路。

## 規約

δ 完全化は Frobenius の逐次余極限で、p 進完備化や一般 f/d 包との比較を含まない。
係数射は raw 包への射と完全化の第零段射の合成で固定する。

## 使われ方

補助包の p 進完備化と、最終 prismatic envelope の比較への検証済み入力。
-/

@[expose] public noncomputable section MonicRawPerfectionFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "F" => deltaAdjoinDivisionStructure E (p : P) a
local notation "j" => monicRawCoefficientMap D f
local notation "C" => DeltaPerfection F
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I

/-- 概要：元の係数環から raw 包への係数射は δ 射。
方針：独立変数の δ 構造の係数包含と δ 除算射を合成する。
規約：φ(f)/p の任意関係族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全化の自然性の入力。 -/
theorem monicRawCoefficient_isDeltaHom : D.IsDeltaHom F j :=
  (deltaAdjoinDivisionMap_isDeltaHom E (p : P) a).comp
    (polynomialRankOneDeltaStructure_C_isDeltaHom σ D)

/-- 概要：補助 raw 包の δ 完全化への実係数射。
方針：既存完全化の第零段射と raw 係数射を合成する。
規約：元の A 作用を明示する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の完全忠実平坦性を定式化する。 -/
def monicRawPerfectionCoefficientMap : A →+* C := deltaAlgebraPerfectionCoefficient F j

/-- 概要：δ 完全化の元の係数射による A 代数構造。
方針：明示的な実係数射から定める。
規約：使用箇所で局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余テンソルの係数を固定する。 -/
@[instance_reducible] def monicRawPerfectionAlgebra : Algebra A C :=
  (monicRawPerfectionCoefficientMap D f).toAlgebra

attribute [local instance] monicRawPerfectionAlgebra

/-- 概要：完全係数環の任意正次数モニック族の δ 完全化の実剰余スカラー拡大は忠実平坦。
方針：raw 包の導来 mod p 入力を一般 δ 完全化の定理に適用する。
規約：一般定理の第二生成元は零とし、元の p 商へ同定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の補助完全化の忠実性。 -/
theorem monicRawPerfection_scalarResidue_faithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    Module.FaithfullyFlat QA ((ModuleCat.extendScalars q).obj
      (baseChangeScalarModule (monicRawPerfectionCoefficientMap D f))) := by
  have hz := monicRaw_modP_homology_isZero D f hD.p_mul_injective hf hdp
  have hFF := monicRaw_modPH0_faithfullyFlat D f hD.p_mul_injective hf hdp hdeg
  have h := deltaAlgebraPerfectionResidueTensor_faithfullyFlat D F j 0 hD
    (monicRawCoefficient_isDeltaHom D f)
    (by rw [Ideal.span_pair_zero]; exact hz) (by rw [Ideal.span_pair_zero]; exact hFF)
  rw [Ideal.span_pair_zero] at h
  exact h

/-- 概要：完全化の制限加群の剰余スカラー拡大は標準 A/p テンソルと線形同型。
方針：二つの標準商比較を合成する。
規約：完全化に明示した同じ係数作用を使用する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の主元判定への入力。 -/
def monicRawPerfection_scalarResidueTensorEquiv :
    ((ModuleCat.extendScalars q).obj
      (baseChangeScalarModule (monicRawPerfectionCoefficientMap D f))) ≃ₗ[QA] QA ⊗[A] C := by
  let M := baseChangeScalarModule (monicRawPerfectionCoefficientMap D f)
  let e : M ≃ₗ[A] C :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (quotientScalarExtensionEquiv I M).trans
    (((quotientModuleFunctor I).mapIso e.toModuleIso).toLinearEquiv.trans
      (quotientTensorReductionEquiv I C).symm)

/-- 概要：δ 完全化の元の係数作用の通常剰余テンソルは忠実平坦。
方針：実剰余スカラー拡大との標準線形同型で移す。
規約：完全 δ 係数環、任意正次数モニック族、δ(p) の単元性を要求する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の主元判定。 -/
theorem monicRawPerfection_residueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    Module.FaithfullyFlat QA (QA ⊗[A] C) := by
  have := monicRawPerfection_scalarResidue_faithfullyFlat D f hD hf hdeg hdp
  exact Module.FaithfullyFlat.of_linearEquiv QA _
    (monicRawPerfection_scalarResidueTensorEquiv D f).symm

/-- 概要：δ 完全化で元の係数環の p スカラーは正則。
方針：完全 δ 環の p 正則性と係数射の自然数保存を使う。
規約：この正則性自体にはモニック性も基底の完全性も不要。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の主元判定の Tor 入力。 -/
theorem monicRawPerfection_p_smul_regular : IsSMulRegular C (p : A) := by
  intro x y h
  apply (deltaPerfection_isPerfect F).p_mul_injective
  simpa only [Algebra.smul_def, map_natCast] using h

/-- 概要：完全係数環上の任意正次数モニック族の補助 δ 完全化は p 完全忠実平坦。
方針：通常剰余テンソルの忠実平坦性と p 正則性を主元判定に渡す。
規約：p 進完備化前の Frobenius 余極限である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の補助包と最終 envelope の比較への準備。 -/
theorem monicRawPerfection_isCompletelyFaithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    IsCompletelyFaithfullyFlat I C :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective C
    (monicRawPerfection_p_smul_regular D f)
    (monicRawPerfection_residueTensor_faithfullyFlat D f hD hf hdeg hdp)

end SerrePositivity.BhattScholze.Andre

end MonicRawPerfectionFlat

/-! ## 補助 raw 包の p 進完備 δ 完全化の忠実平坦性

## 概要

完全 δ 係数環上の任意正次数モニック族について、補助 raw φ(f)/p 包の p 進完備 δ 完全化は
元の係数射に関して p 完全忠実平坦。BS 著者版 Corollary 2.39（著者版 p.25）、BS 著者版 Remark 7.15（p.62）の準備。

## 方針

完備化の開イデアル商の比較で mod p の忠実平坦性を保ち、完全 δ 構造の p 正則性を使う。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の補助計算。

## 規約

対象は補助 φ(f)/p 包の完全化である。一般 f/d 包やその perfectoid 商との比較は含まない。

## 使われ方

最終 prismatic envelope の比較への補助的な p 完全忠実平坦性を供給する。
-/

@[expose] public noncomputable section MonicRawPCompletionFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun s : σ => monicRelation (f s) s)
local notation "F" => deltaAdjoinDivisionStructure E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "C" => DeltaPerfection F
local notation "Z" => PCompletedDeltaPerfection F
local notation "I" => Ideal.span ({(p : A)} : Set A)
local notation "J" => Ideal.span ({(p : C)} : Set C)
local notation "Q" => A ⧸ I

/-- 概要：既存完備化の、完備化前の実δ完全化に関する標準代数構造。
方針：標準の古典的 p 進完備化の代数構造を使用する。
規約：局所導入し、元の係数作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化前後の剰余比較。 -/
abbrev monicRawPCompletedPerfectionOverPerfection : Algebra C Z :=
  inferInstanceAs (Algebra C (AdicCompletion J C))

/-- 概要：元のraw係数射と既存のp進完備δ完全化標準射の合成。
方針：元の raw 係数射と既存の完備化射を合成する。
規約：実際の元の A 係数射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の基底上の平坦性。 -/
def monicRawPCompletedPerfectionCoefficientMap : A →+* Z :=
  (pCompletedDeltaPerfectionMap F).comp (monicRawCoefficientMap D f)

/-- 概要：p進完備δ完全化の実A係数作用。
方針：明示した係数射から代数構造を定める。
規約：局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余テンソルの元の係数作用。 -/
abbrev monicRawPCompletedPerfectionAlgebra : Algebra A Z :=
  (monicRawPCompletedPerfectionCoefficientMap D f).toAlgebra

attribute [local instance] monicRawPerfectionAlgebra monicRawPCompletedPerfectionAlgebra
  adicQuotientAlgebra monicRawPCompletedPerfectionOverPerfection
local notation "Kc" => Ideal.map (algebraMap A C) I
local notation "Kz" => Ideal.map (algebraMap A Z) I

/-- 概要：実係数作用は、完備化前の係数射と標準完備化射の合成。
方針：定義の一致による。
規約：第零段射の係数作用を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化前後の係数比較。 -/
theorem monicRawPCompletedPerfectionCoefficientMap_comp :
    monicRawPCompletedPerfectionCoefficientMap D f =
      (algebraMap C Z).comp (monicRawPerfectionCoefficientMap D f) := rfl

/-- 概要：正確なA係数のp商を、完備化前後で比較する実環同型。
方針：拡張イデアルを p 主イデアルと同定し、開商の比較を使う。
規約：商環だけでなく元の係数像も次の補題で保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のmod p 忠実平坦性の保存。 -/
def monicRawPCompletedPerfectionResidueEquiv : Z ⧸ Kz ≃+* C ⧸ Kc := by
  have hc : Kc = J := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hz : Kz = Ideal.map (algebraMap C Z) J := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.map_span, Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq hz).trans
    ((adicCompletionOpenQuotientEquiv J J 1 (by simp)
      (Submodule.fg_span (Set.toFinite _))).toRingEquiv.trans (Ideal.quotEquivOfEq hc.symm))

/-- 概要：実剰余同型は、元の完備化前の標準係数像を保つ。
方針：開商比較の標準完備化射に関する公式を使う。
規約：任意の完備化前の元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/p 作用の比較。 -/
theorem monicRawPCompletedPerfectionResidueEquiv_mk (c : C) :
    monicRawPCompletedPerfectionResidueEquiv D f
      (Ideal.Quotient.mk Kz (algebraMap C Z c)) = Ideal.Quotient.mk Kc c := by
  unfold monicRawPCompletedPerfectionResidueEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change Ideal.quotEquivOfEq _
    (adicCompletionOpenQuotientMap J J 1 (by simp) (algebraMap C Z c)) = _
  rw [adicCompletionOpenQuotientMap_algebraMap, Ideal.quotEquivOfEq_mk]

local instance monicRawPCompletedPerfectionResidueAlgebra : Algebra Q (Z ⧸ Kz) :=
  adicQuotientAlgebra I Z
local instance monicRawPerfectionActualResidueAlgebra : Algebra Q (C ⧸ Kc) :=
  adicQuotientAlgebra I C

local instance monicRawPCompletedPerfectionResidueModule : Module Q (Z ⧸ Kz) := Algebra.toModule
local instance monicRawPerfectionActualResidueModule : Module Q (C ⧸ Kc) := Algebra.toModule

set_option maxHeartbeats 800000 in
-- 完備化前後の具体的商作用と係数射の照合に、既定値を超える簡約を要する。
/-- 概要：剰余比較は、元のA/pの標準作用について線形。
方針：剰余係数を代表元へ戻し、係数像の公式を使う。
規約：元の係数作用を別の作用に取り替えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の忠実平坦性の移送。 -/
def monicRawPCompletedPerfectionResidueLinearEquiv : (Z ⧸ Kz) ≃ₗ[Q] C ⧸ Kc := by
  let : IsScalarTower A C Z := IsScalarTower.of_algebraMap_eq' rfl
  refine { (monicRawPCompletedPerfectionResidueEquiv D f).toAddEquiv with map_smul' := ?_ }
  intro c x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  change monicRawPCompletedPerfectionResidueEquiv D f
    ((Ideal.Quotient.mk Kz (algebraMap A Z c)) * x) =
      (Ideal.Quotient.mk Kc (algebraMap A C c)) *
        monicRawPCompletedPerfectionResidueEquiv D f x
  rw [map_mul, IsScalarTower.algebraMap_apply A C Z,
    monicRawPCompletedPerfectionResidueEquiv_mk]

/-- 概要：通常の正確な標準剰余テンソルも、完備化前後でA/p線形に同型。
方針：商テンソル比較と剰余の線形比較を合成する。
規約：元の標準係数射に沿う通常テンソルを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の主元判定の剰余入力。 -/
def monicRawPCompletedPerfectionResidueTensorEquiv :
    (Q ⊗[A] Z) ≃ₗ[Q] Q ⊗[A] C :=
  ((quotientTensorReductionEquiv I Z).trans (adicReductionEquivAlgebraQuotient I Z)).trans
    ((monicRawPCompletedPerfectionResidueLinearEquiv D f).trans
      ((quotientTensorReductionEquiv I C).trans (adicReductionEquivAlgebraQuotient I C)).symm)

/-- 概要：通常剰余テンソルの忠実平坦性は、既存p進完備δ完全化へ保存される。
方針：前工程の δ 完全化の忠実平坦性を標準剰余線形比較で移す。
規約：完全基底上の正次数モニック任意族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の補助包の p 完全忠実平坦性。 -/
theorem monicRawPCompletedPerfection_residueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    Module.FaithfullyFlat Q (Q ⊗[A] Z) := by
  have := monicRawPerfection_residueTensor_faithfullyFlat D f hD hf hdeg hdp
  exact Module.FaithfullyFlat.of_linearEquiv Q (Q ⊗[A] C)
    (monicRawPCompletedPerfectionResidueTensorEquiv D f)

/-- 概要：p進完備δ完全化のp正則性は、元のAのpスカラーについても成り立つ。
方針：完全 δ 構造の p 正則性と係数射の自然数保存を使う。
規約：この正則性にはモニック性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の主元判定の Tor 消滅入力。 -/
theorem monicRawPCompletedPerfection_p_smul_regular : IsSMulRegular Z (p : A) := by
  intro x y h
  apply (pCompletedDeltaPerfection_isPerfect F).p_mul_injective
  simp only [Algebra.smul_def, map_natCast] at h
  exact h

/-- 概要：完全係数環の任意正次数モニック族の補助 raw 包の p 進完備 δ 完全化は p 完全忠実平坦。
方針：p 正則性と通常剰余テンソルの忠実平坦性を主元判定に渡す。
規約：正次数モニック族の補助 φ(f)/p 包の結果である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終 f/d 包との比較への準備。 -/
theorem monicRawPCompletedPerfection_isCompletelyFaithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    IsCompletelyFaithfullyFlat I Z :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective Z
    (monicRawPCompletedPerfection_p_smul_regular D f)
    (monicRawPCompletedPerfection_residueTensor_faithfullyFlat D f hD hf hdeg hdp)

end SerrePositivity.BhattScholze.Andre

end MonicRawPCompletionFlat

/-! ## 任意の整 perfectoid 基底上のモニック根付き拡大

## 概要

任意の整 perfectoid 環上の任意正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一段構成。

## 方針

非零枝では Fontaine 写像の核の実 PD 完備化から完全 prism 商表示を得る。
商表示へ多項式を移して任意族の構成を適用し、環同型に沿って基底作用と根を戻す。
零枝は自己拡大を使う。原典の BS 著者版 Proposition 7.11 による証明とは異なる PD 計算の経路である。

## 規約

各多項式に正次数を要求する。基底の表示・p 正則性・ねじれなし、族全体の有限性を仮定しない。

## 使われ方

有界深さ有限部分族の実余極限と完備化を使う、一段の全根添加を供給する。
-/

@[expose] public noncomputable section MonicRootedPerfectoidExtension

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion

/-- 概要：任意の整 perfectoid 基底上の任意正次数モニック族に、全根を持つ拡大がある。
方針：完全 prism 商表示で任意族の拡大を構成し、基底環同型と評価の自然性で戻す。
規約：補助的な忠実平坦性や基底表示、族全体の有限性を仮定しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一段構成。 -/
theorem exists_monicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  rcases hR with hs | ⟨hp, hc, ⟨π, v, hv⟩, hF, hker⟩
  · let := hs
    refine ⟨R, inferInstance, RingHom.id R, fun _ => 0, Or.inl hs, ?_, ?_⟩
    · exact monicRootedBase_self_isCompletelyFaithfullyFlat _
    · intro s
      exact Subsingleton.elim _ _
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hker π v hv
    let := pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    let F := fun s => (f s).map e.symm.toRingHom
    have hFm : ∀ s, (F s).Monic := fun s => (hf s).map _
    have hFd : ∀ s, 0 < (F s).natDegree := by
      intro s
      rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
      exact hdeg s
    obtain ⟨T, hT, g, ρ, hperf, hflat, hroot⟩ :=
      exists_monicRootedPerfectoidExtension_of_perfectPrism P hP F hFm hFd
    let := hT
    exact ⟨T, hT, g.comp e.symm.toRingHom, ρ,
      monicRootedExtension_of_baseEquiv p e.symm f g ρ hperf hflat hroot⟩

end SerrePositivity.BhattScholze.Andre

end MonicRootedPerfectoidExtension
