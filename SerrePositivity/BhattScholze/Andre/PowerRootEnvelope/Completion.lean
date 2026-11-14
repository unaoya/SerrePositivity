module
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.RegularReduction
public import SerrePositivity.BhattScholze.Delta.Extension.PDCompletionCoordinates

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# 完備化の比較と完全平坦性の還元

## 概要
正則主剰余・正則主環商から二元完全平坦性を戻すこと、二段の主剰余の忠実平坦性、座標を保つ同型による導来完備化の比較、両座標を殺す商と H⁰、二元係数剰余、p 完備化の普遍性・主商・交換。
BS 著者版 Remark 7.15 の被覆の計算に使う、完備化の比較と完全平坦性の判定を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/DeltaDivisionWitt`、`PowerRootEnvelope/PerfectionFaithful`、`PowerRootEnvelope/PowerRootInput`、`PowerRootEnvelope/VarpiComparison`、`Variants/Auxiliary`。
-/

universe u v

/-! ## 正則主剰余から二元完全平坦性を戻す

## 概要

d が基底環と係数加群で正則なら、mod d の a 完全平坦性から元の (a,d) 完全平坦性が従う。
BS 著者版 Remark 7.15（著者版 p.62）の実候補の導来剰余を δ 完全化へ渡す一般計算。

## 方針

正則性で mod d の高次 Tor を消し、d で消える試験加群の Tor を底変換後に計算する。

## 規約

完備性・Noether 性・通常平坦性は要求しない。

## 使われ方

H/d の p 完全平坦性を実完備化 H の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section CompletelyFlatRegularReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

/-- 概要：完全平坦な加群の定義イデアルによる標準底変換は高次 Tor を持たない。
方針：イデアルで消える標準係数加群を試験加群に取って Tor の対称性を使う。
規約：イデアルは任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実導来還元の離散性。 -/
theorem scalarExtensionTorVanishing_of_completelyFlat
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : IsCompletelyFlat I M) : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M := by
  let : Module R (R ⧸ I) := Module.compHom (R ⧸ I) (Ideal.Quotient.mk I)
  have hN : ∀ r ∈ I, ∀ x : R ⧸ I, r • x = 0 := by
    intro r hr x
    change Ideal.Quotient.mk I r * x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  intro i hi
  have : Subsingleton (TorModule R i M (R ⧸ I)) :=
    (isConcentratedInDegreeZero_derivedTensor_iff M (R ⧸ I)).mp (hM (R ⧸ I) hN) i hi
  have : Subsingleton (TorModule R i (R ⧸ I) M) :=
    (torModuleComm (R := R) i (R ⧸ I) M).injective.subsingleton
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R (R ⧸ I))).obj M) :=
    ModuleCat.isZero_of_subsingleton _
  let e : baseChangeScalarModule (Ideal.Quotient.mk I) ≃ₗ[R] (R ⧸ I) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact hz.of_iso (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app M)

end SerrePositivity.BhattScholze.Andre

end CompletelyFlatRegularReduction

/-! ## 正則主環商から二元完全平坦性を戻す

## 概要

可換代数の正則主環商の完全平坦性を、元の係数作用に関する二元完全平坦性へ移す。
BS 著者版 Remark 7.15（著者版 p.62）の自然な実候補の導来剰余への接続。

## 方針

標準スカラー拡大と通常主環商の線形同型を作り、正則主剰余の一般判定を使う。

## 規約

基底環と代数での分母正則性を明示する。通常平坦性や Noether 性は不要。

## 使われ方

自然な Hodge–Tate 候補の p 完全平坦性を元の実完備化の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section CompletelyFaithfulPairReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
open scoped TensorProduct

/-- 概要：完全忠実平坦性は標準スカラー拡大の忠実平坦性を与える。
方針：定義中の通常テンソルと標準剰余加群の線形同型を使う。
規約：イデアルは任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ への移送。 -/
theorem scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : IsCompletelyFaithfullyFlat I M) :
    Module.FaithfullyFlat (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) := by
  let := hM.2
  let e := (quotientScalarExtensionEquiv I M).trans (quotientTensorReductionEquiv I M).symm
  exact Module.FaithfullyFlat.of_linearEquiv _ ((R ⧸ I) ⊗[R] M) e

/-- 概要：mod d の a 完全忠実平坦性から元の二元剰余は忠実平坦。
方針：二重主商の同型に沿う底変換とスカラー拡大の合成同型を使う。
規約：元の加群の正則性・完備性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の導来二元剰余 H⁰ の係数作用。 -/
theorem pairScalarExtension_faithfullyFlat_of_principal_reduction
    {R : Type u} [CommRing R] (a d : R) (M : ModuleCat.{u} R)
    (hred : IsCompletelyFaithfullyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) a})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj M)) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a, d}))).obj M) := by
  let qd := Ideal.Quotient.mk (Ideal.span {d})
  let qa := Ideal.Quotient.mk (Ideal.span {qd a})
  let q := Ideal.Quotient.mk (Ideal.span {a, d})
  have hswap : Ideal.span {d, a} = Ideal.span {a, d} := by rw [Set.pair_comm]
  let eQ := (principalDoubleQuotEquiv d a).trans (Ideal.quotEquivOfEq hswap)
  let k := eQ.toRingHom
  let := k.toAlgebra
  let N := (ModuleCat.extendScalars qa).obj ((ModuleCat.extendScalars qd).obj M)
  have : Module.FaithfullyFlat ((R ⧸ Ideal.span {d}) ⧸ Ideal.span {qd a}) N :=
    scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat _ _ hred
  have hF : Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
      ((ModuleCat.extendScalars k).obj N) := by
    change Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
      ((R ⧸ Ideal.span {a, d}) ⊗[(R ⧸ Ideal.span {d}) ⧸ Ideal.span {qd a}] N)
    infer_instance
  have heq : k.comp (qa.comp qd) = q := by
    apply RingHom.ext
    intro r
    change eQ (qa (qd r)) = q r
    change (Ideal.quotEquivOfEq hswap) (principalDoubleQuotEquiv d a (qa (qd r))) = q r
    rw [principalDoubleQuotEquiv_mk, Ideal.quotEquivOfEq_mk]
  let e : (ModuleCat.extendScalars q).obj M ≅ (ModuleCat.extendScalars k).obj N :=
    eqToIso (congrArg (fun g => (ModuleCat.extendScalars g).obj M) heq.symm) ≪≫
      (ModuleCat.extendScalarsComp (qa.comp qd) k).app M ≪≫
      (ModuleCat.extendScalars k).mapIso ((ModuleCat.extendScalarsComp qd qa).app M)
  let := hF
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars k).obj N)
    e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end CompletelyFaithfulPairReduction

/-! ## 座標を保つ環同型による実導来完備化の比較

## 概要

環射が d を d' に送れば、実導来 (p,d) 完備化の H⁰ から (p,d') 完備化の H⁰ へ
標準係数射を保つ一意な環射がある。元の射が環同型なら延長も環同型。
BS 著者版 Remark 7.15（著者版 p.62）の raw 比較を完備化へ通すための一般計算。

## 方針

既存の実導来完備性と H⁰ の環としての普遍性を使う。
逆合成は標準単位との合成で一致することから一意性で確認する。

## 規約

実際の PDCompletionH0 と既存の環構造・単位を使い、正則性を追加しない。

## 使われ方

raw δ 包の係数自己同型による比較を、指定生成元の完備化の比較へ延長する。
-/

@[expose] public noncomputable section PDCompletionKilledCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] (p : ℕ) (d : A) (I : Ideal A)
variable (hpI : (p : A) ∈ I) (hdI : d ∈ I)
local notation "H" => PDCompletionH0 A p d
local notation "uA" => pdCompletionUnit A p d
local notation "J" => Ideal.map (pdCompletionUnit A p d) I

private theorem moduleComplete_of_scalar_zero (T : Type u) [CommRing T]
    (z : T) (hz : z = 0) : IsModuleComplete T z (ModuleCat.of T T) := by
  apply isModuleComplete_of_pow_smul_zero T z (ModuleCat.of T T) 1
  simp [hz]

include hpI hdI in
/-- 概要：両座標を殺す商への標準係数射は実 H⁰ から一意に延長する。
方針：商での p,d の消滅による導来完備性を環普遍性へ渡す。
規約：I は p と d を含む任意のイデアル。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余比較の逆射。 -/
theorem existsUnique_pdCompletionKilledCoordinateMap :
    letI := pdCompletionCommRing A p d
    ∃! F : H →+* A ⧸ I, F.comp uA = Ideal.Quotient.mk I := by
  let := pdCompletionCommRing A p d
  apply existsUnique_pdCompletionRingHom A p d (A ⧸ I) (Ideal.Quotient.mk I)
  · apply moduleComplete_of_scalar_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  · apply moduleComplete_of_scalar_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hdI

/-- 概要：実完備化から両座標を殺す商への標準延長を選ぶ。
方針：一意延長の存在から選択する。
規約：指定した元の商射を延長する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商比較の構成。 -/
def pdCompletionKilledCoordinateMap :
    letI := pdCompletionCommRing A p d
    H →+* A ⧸ I := by
  let := pdCompletionCommRing A p d
  exact (existsUnique_pdCompletionKilledCoordinateMap p d I hpI hdI).choose

/-- 概要：選択した延長は標準完備化単位との合成で元の商射になる。
方針：選択した射の仕様を使う。
規約：環射の合成の等式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数上の逆合成。 -/
theorem pdCompletionKilledCoordinateMap_comp_unit :
    letI := pdCompletionCommRing A p d
    (pdCompletionKilledCoordinateMap p d I hpI hdI).comp uA = Ideal.Quotient.mk I := by
  let := pdCompletionCommRing A p d
  exact (existsUnique_pdCompletionKilledCoordinateMap p d I hpI hdI).choose_spec.1

/-- 概要：標準延長は各係数元の完備化像を同じ商代表元へ送る。
方針：標準単位との合成公式を各元で評価する。
規約：元の商射の値を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の代表元での剰余比較。 -/
theorem pdCompletionKilledCoordinateMap_unit (b : A) :
    letI := pdCompletionCommRing A p d
    pdCompletionKilledCoordinateMap p d I hpI hdI (uA b) = Ideal.Quotient.mk I b := by
  let := pdCompletionCommRing A p d
  exact RingHom.congr_fun (pdCompletionKilledCoordinateMap_comp_unit p d I hpI hdI) b

/-- 概要：元の係数商から実完備化の像イデアル商への標準環射。
方針：I の係数像がその像イデアルに属することから商へ降ろす。
規約：p,d を含むことは順射自体には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余比較の順射。 -/
def pdCompletionQuotientFromRaw :
    letI := pdCompletionCommRing A p d
    (A ⧸ I) →+* H ⧸ J := by
  let := pdCompletionCommRing A p d
  apply Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp uA)
  intro b hb
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem uA hb)

/-- 概要：標準順射は元の代表元をその標準完備化像の商へ送る。
方針：商射の定義を使う。
規約：全ての b:A を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実係数射の照合。 -/
theorem pdCompletionQuotientFromRaw_mk (b : A) :
    letI := pdCompletionCommRing A p d
    pdCompletionQuotientFromRaw p d I (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk J (uA b) := rfl

/-- 概要：実完備化の像イデアル商から元の商への逆射。
方針：標準延長が I の全ての像を殺すことを使う。
規約：像イデアル全体を殺すことを商の普遍性へ渡す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余比較。 -/
def pdCompletionQuotientToRaw :
    letI := pdCompletionCommRing A p d
    (H ⧸ J) →+* A ⧸ I := by
  let := pdCompletionCommRing A p d
  apply Ideal.Quotient.lift J (pdCompletionKilledCoordinateMap p d I hpI hdI)
  have hle : J ≤ RingHom.ker (pdCompletionKilledCoordinateMap p d I hpI hdI) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change pdCompletionKilledCoordinateMap p d I hpI hdI (uA b) = 0
    rw [pdCompletionKilledCoordinateMap_unit]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  exact fun b hb => hle hb

/-- 概要：逆射は完備化の代表元を標準延長で送る。
方針：商に降ろした射の定義を使う。
規約：元の実 H⁰ の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一意性による逆合成。 -/
theorem pdCompletionQuotientToRaw_mk (t : H) :
    letI := pdCompletionCommRing A p d
    pdCompletionQuotientToRaw p d I hpI hdI (Ideal.Quotient.mk J t) =
      pdCompletionKilledCoordinateMap p d I hpI hdI t := rfl

/-- 概要：元の商から完備化の商へ送り戻す合成は恒等射。
方針：元の環の代表元で標準延長の係数公式を使う。
規約：商射の全射性による外延性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余環同型の片側逆。 -/
theorem pdCompletionQuotientToRaw_comp_fromRaw :
    letI := pdCompletionCommRing A p d
    (pdCompletionQuotientToRaw p d I hpI hdI).comp (pdCompletionQuotientFromRaw p d I) =
      RingHom.id (A ⧸ I) := by
  let := pdCompletionCommRing A p d
  apply Ideal.Quotient.ringHom_ext
  ext b
  change pdCompletionQuotientToRaw p d I hpI hdI
    (pdCompletionQuotientFromRaw p d I (Ideal.Quotient.mk I b)) = Ideal.Quotient.mk I b
  rw [pdCompletionQuotientFromRaw_mk, pdCompletionQuotientToRaw_mk]
  exact RingHom.congr_fun (pdCompletionKilledCoordinateMap_comp_unit p d I hpI hdI) b

/-- 概要：完備化の商から元の商へ送り戻す合成も恒等射。
方針：像イデアル商では両座標が零なので実完備化の一意性を適用する。
規約：単なる係数一致を全射性なしに一意延長の等式へ移す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余環同型のもう片側逆。 -/
theorem pdCompletionQuotientFromRaw_comp_toRaw :
    letI := pdCompletionCommRing A p d
    (pdCompletionQuotientFromRaw p d I).comp (pdCompletionQuotientToRaw p d I hpI hdI) =
      RingHom.id (H ⧸ J) := by
  let := pdCompletionCommRing A p d
  let g := (Ideal.Quotient.mk J).comp uA
  have hz (b : A) (hb : b ∈ I) : g b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem uA hb)
  have hpQ : (p : H ⧸ J) = 0 := by
    simpa only [g, RingHom.comp_apply, map_natCast] using hz (p : A) hpI
  apply Ideal.Quotient.ringHom_ext
  change (pdCompletionQuotientFromRaw p d I).comp
    (pdCompletionKilledCoordinateMap p d I hpI hdI) = Ideal.Quotient.mk J
  apply pdCompletionRingHom_ext A p d (H ⧸ J) g
    (moduleComplete_of_scalar_zero _ _ hpQ) (moduleComplete_of_scalar_zero _ _ (hz d hdI))
  · ext b
    change pdCompletionQuotientFromRaw p d I
      (pdCompletionKilledCoordinateMap p d I hpI hdI (uA b)) = g b
    rw [pdCompletionKilledCoordinateMap_unit, pdCompletionQuotientFromRaw_mk]
    rfl
  · rfl

/-- 概要：両座標を殺す商は実導来完備化 H⁰ の前後で環同型。
方針：標準順射と逆射の二つの逆合成を束ねる。
規約：正則性の追加仮定を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余を raw 剰余へ戻す同型。 -/
def pdCompletionQuotientEquivOfKilledCoordinates :
    letI := pdCompletionCommRing A p d
    (H ⧸ J) ≃+* A ⧸ I := by
  let := pdCompletionCommRing A p d
  exact RingEquiv.ofRingHom (pdCompletionQuotientToRaw p d I hpI hdI)
    (pdCompletionQuotientFromRaw p d I)
    (pdCompletionQuotientToRaw_comp_fromRaw p d I hpI hdI)
    (pdCompletionQuotientFromRaw_comp_toRaw p d I hpI hdI)

/-- 概要：剰余比較同型は元の係数の標準完備化像を同じ商代表元へ送る。
方針：逆射の代表元公式と標準延長の仕様を使う。
規約：元の商射との可換性を全 b:A で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包への係数を保つ接続。 -/
theorem pdCompletionQuotientEquivOfKilledCoordinates_unit (b : A) :
    letI := pdCompletionCommRing A p d
    pdCompletionQuotientEquivOfKilledCoordinates p d I hpI hdI
      (Ideal.Quotient.mk J (uA b)) = Ideal.Quotient.mk I b := by
  let := pdCompletionCommRing A p d
  exact RingHom.congr_fun (pdCompletionKilledCoordinateMap_comp_unit p d I hpI hdI) b

end SerrePositivity.BhattScholze.Andre

end PDCompletionKilledCoordinates

/-! ## 実完備化の二元係数剰余と未完備の剰余

## 概要

c が (p,d) に属すれば、実導来 (p,c) 完備化 H⁰ の (p,d) 商は元の環の (p,d) 商と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 側の完備化剰余へ使う。

## 方針

二元係数イデアルの像を計算し、両完備化座標を殺す一般商比較を適用する。

## 規約

c や d の正則性は不要。実 H⁰ と標準単位を保持する。

## 使われ方

c=φ(d) として、完備化後の (p,d) 商を raw 包の (p,d) 商へ戻す。
-/

@[expose] public noncomputable section PDCompletionPairResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] (p : ℕ) (c d : A)
local notation "H" => PDCompletionH0 A p c
local notation "uA" => pdCompletionUnit A p c

/-- 概要：二元イデアル (p,d) の完備化像は同じ二つの標準像で生成される。
方針：span の像と環射の自然数保存性を使う。
規約：右辺の p は実 H⁰ 内の自然数。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二元商の係数像の同定。 -/
theorem pdCompletionPairIdeal_map :
    letI := pdCompletionCommRing A p c
    (Ideal.span {(p : A), d}).map uA = Ideal.span {(p : H), uA d} := by
  let := pdCompletionCommRing A p c
  rw [Ideal.map_span, Set.image_pair, map_natCast]

/-- 概要：c が (p,d) に属せば実完備化の (p,d) 商は元の二元商と環同型。
方針：像イデアルの等式と両座標を殺す商の一般同型を合成する。
規約：正則性・非零性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化剰余を未完備の剰余へ戻す。 -/
def pdCompletionPairResidueEquiv (hc : c ∈ Ideal.span {(p : A), d}) :
    letI := pdCompletionCommRing A p c
    (H ⧸ Ideal.span {(p : H), uA d}) ≃+* (A ⧸ Ideal.span {(p : A), d}) := by
  let := pdCompletionCommRing A p c
  exact (Ideal.quotEquivOfEq (pdCompletionPairIdeal_map p c d).symm).trans
    (pdCompletionQuotientEquivOfKilledCoordinates p c (Ideal.span {(p : A), d})
      (Ideal.subset_span (by simp)) hc)

/-- 概要：二元剰余比較同型は標準完備化像を元の代表元へ送る。
方針：像イデアルの商同型と一般商比較の単位公式を使う。
規約：全ての b:A を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 係数を保つ比較。 -/
theorem pdCompletionPairResidueEquiv_unit
    (hc : c ∈ Ideal.span {(p : A), d}) (b : A) :
    letI := pdCompletionCommRing A p c
    pdCompletionPairResidueEquiv p c d hc (Ideal.Quotient.mk _ (uA b)) =
      Ideal.Quotient.mk _ b := by
  let := pdCompletionCommRing A p c
  simp only [pdCompletionPairResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    pdCompletionQuotientEquivOfKilledCoordinates_unit]

end SerrePositivity.BhattScholze.Andre

end PDCompletionPairResidue

/-! ## André p 完備化から完備環への環射

## 概要

通常の p 完備化から p 完備環への環射は、元の環からの射に一意に対応する。
BS 著者版 Remark 7.15（著者版 p.62）の完備入力環の試験射に使う。

## 方針

指定環射で標的を代数にし、有限生成イデアルの完備代数への既存の普遍性を適用する。
原典の記述を補う、通常の加群完備化と係数射による経路。

## 規約

p の素数性・源の p 正則性は不要。標的には通常の p 完備性を要求する。

## 使われ方

未完備入力商からの射を、その p 完備化からの射へ延長する。
-/

@[expose] public noncomputable section PrimeAdicCompletionUniversal

namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R] (p : ℕ)
variable {B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]
local notation "C" => AdicCompletion (Ideal.span {(p : R)}) R

/-- 概要：元の環射は p 完備化から p 完備環への一意な環射に延長する。
方針：環射で指定した代数作用のもとで、完備代数への一意な代数射を環射に戻す。
規約：p 正則性や Noether 性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力環からの射。 -/
theorem existsUnique_primeAdicCompletionHom (k : R →+* B) :
    ∃! F : C →+* B, F.comp (algebraMap R C) = k := by
  let := k.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) B := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := B) (M := B)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
      (inferInstance : IsAdicComplete (Ideal.span {(p : B)}) B)
  obtain ⟨F, _, hu⟩ := adicCompletion_existsUnique_algHom R
    (Ideal.span {(p : R)}) (Submodule.fg_span_singleton _) B
  refine ⟨F.toRingHom, ?_, ?_⟩
  · exact RingHom.ext F.commutes
  · intro G hG
    let G' : C →ₐ[R] B := { G with commutes' := RingHom.congr_fun hG }
    exact congrArg AlgHom.toRingHom (hu G' trivial)

/-- 概要：p 完備化から p 完備環への環射は元の環上の値で決まる。
方針：同じ元の環射を延長する二つの射の一意性を使う。
規約：環射に連続性を追加指定する必要はない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力射の一意性。 -/
theorem primeAdicCompletion_ringHom_ext (F G : C →+* B)
    (h : F.comp (algebraMap R C) = G.comp (algebraMap R C)) : F = G := by
  obtain ⟨K, _, hu⟩ := existsUnique_primeAdicCompletionHom R p (G.comp (algebraMap R C))
  exact (hu F h).trans (hu G rfl).symm

end SerrePositivity.BhattScholze.Andre

end PrimeAdicCompletionUniversal

/-! ## André 全冪商で正則な入力による完備化の商

## 概要

各 p 冪商で正則な入力を使うと、p 完備化をその入力で割った環も p 完備となる。
BS 著者版 Remark 7.15（著者版 p.62）のモニック商と完備化の交換への準備。

## 方針

全冪商の正則性から乗法のフィルトレーション比較を直接得る。
完備化の冪商比較で同じ正則性を完備環へ移す。原典を補う一様な比較による経路。

## 規約

p 正則性・Noether 性・素数性を前提としない。全冪商の入力の正則性を明示する。

## 使われ方

モニック入力の全係数冪商での正則性を供給し、原典の完備入力環を接続する。
-/

@[expose] public noncomputable section PrimeAdicCompletionPrincipalQuotient

namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R]

/-- 概要：全ての a 冪商で正則な元による商は a 完備。
方針：各冪商の正則性で乗法写像の逆像のフィルトレーションを比較する。
規約：a 自体の正則性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック商の完備性。 -/
theorem isAdicComplete_principal_quotient_of_regular_powers (a g : R)
    [IsAdicComplete (Ideal.span {a}) R]
    (hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {a ^ n})
      (Ideal.Quotient.mk (Ideal.span {a ^ n}) g)) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a})
      (R ⧸ Ideal.span {g}) := by
  let m := LinearMap.mulLeft R g
  have hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap m ((Ideal.span {a}) ^ (n + k) • (⊤ : Submodule R R)) ≤
        (Ideal.span {a}) ^ n • (⊤ : Submodule R R) := by
    refine ⟨0, fun n x hx => ?_⟩
    simp only [Submodule.mem_comap, m, LinearMap.mulLeft_apply, Nat.add_zero,
      Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      at hx ⊢
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hg n
    change Ideal.Quotient.mk (Ideal.span {a ^ n}) g *
      Ideal.Quotient.mk (Ideal.span {a ^ n}) x =
        Ideal.Quotient.mk (Ideal.span {a ^ n}) g * 0
    rw [← map_mul, mul_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)
  have hrange : m.range = (Ideal.span {g} : Submodule R R) := by
    ext x
    simp only [LinearMap.mem_range, m, LinearMap.mulLeft_apply,
      Ideal.mem_span_singleton, dvd_def]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  let : IsAdicComplete (Ideal.span {a}) (R ⧸ Ideal.span {g}) := by
    rw [← hrange]
    exact isAdicComplete_quotient_range_of_uniform_filtration_bound (Ideal.span {a}) m hbound
  have he : (Ideal.span {a}).map (algebraMap R (R ⧸ Ideal.span {g})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← he]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

variable (p : ℕ)
local notation "Jp" => Ideal.span {(p : R)}
local notation "C" => AdicCompletion Jp R
local notation "j" => algebraMap R C

/-- 概要：p 完備化はその環上の p 主イデアルに関して完備。
方針：有限生成性による完備性をイデアルの拡張で移す。
規約：係数環上の加群完備性と環自身の完備性を明示的に比較する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力環。 -/
theorem primeAdicCompletion_isAdicComplete : IsAdicComplete (Ideal.span {(p : C)}) C := by
  have h := (IsAdicComplete.map_algebraMap_iff (I := Jp) (S := C) (M := C)).mpr
    (AdicCompletion.isAdicComplete (M := R) (Submodule.fg_span_singleton (p : R)))
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h

/-- 概要：入力の p 冪商での正則性は p 完備化の同じ冪商で保存される。
方針：完備化の冪商同型と代表元公式で正則性を移す。
規約：p 自体の正則性は使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後のモニック入力。 -/
theorem primeAdicCompletion_regular_mod_power (g : R) (n : ℕ)
    (hg : IsSMulRegular (R ⧸ Ideal.span {(p : R) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) g)) :
    IsSMulRegular (C ⧸ Ideal.span {(p : C) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : C) ^ n}) (j g)) := by
  have hr : IsSMulRegular (R ⧸ Jp ^ n) (Ideal.Quotient.mk (Jp ^ n) g) := by
    rw [Ideal.span_singleton_pow]
    exact hg
  have h : IsSMulRegular (C ⧸ ((Jp).map j) ^ n)
      (Ideal.Quotient.mk (((Jp).map j) ^ n) (j g)) := by
    let e := adicCompletionPowQuotientEquiv Jp (Submodule.fg_span_singleton (p : R)) n
    intro x y hxy
    apply e.injective
    apply hr
    have he := congrArg e hxy
    have hc : e (Ideal.Quotient.mk (((Jp).map j) ^ n) (j g)) =
        Ideal.Quotient.mk (Jp ^ n) g :=
      adicCompletionPowQuotientEquiv_algebraMap Jp (Submodule.fg_span_singleton (p : R)) n g
    simpa only [smul_eq_mul, map_mul, hc] using he
  rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_pow] at h
  exact h

/-- 概要：全 p 冪商で正則な入力を p 完備化で割ると p 完備環を得る。
方針：冪商の正則性を完備化へ移し、一様なフィルトレーション比較を適用する。
規約：源の p 正則性や有界 p ねじれを追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化と入力商の交換。 -/
theorem primeAdicCompletion_principal_quotient_isAdicComplete (g : R)
    (hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {(p : R) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) g)) :
    IsAdicComplete (Ideal.span {(p : C ⧸ Ideal.span {j g})})
      (C ⧸ Ideal.span {j g}) := by
  let := primeAdicCompletion_isAdicComplete R p
  have h := isAdicComplete_principal_quotient_of_regular_powers C (p : C) (j g)
    (fun n => primeAdicCompletion_regular_mod_power R p g n (hg n))
  simpa only [map_natCast] using h

end SerrePositivity.BhattScholze.Andre

end PrimeAdicCompletionPrincipalQuotient

/-! ## André 全冪商で正則な主関係と p 完備化の交換

## 概要

入力 g が全 p 冪商で正則なら、p 完備化を g で割る操作と g 商を p 完備化する操作は
元の係数射を保つ環同型で結ばれる。BS 著者版 Remark 7.15（著者版 p.62）の完備入力環。

## 方針

完備化後の主商の完備性を証明済みの一様な比較から得る。
両方向の射を完備化と商の普遍性で構成し、一意性で互いに逆と示す。
原典の記述を補う環射の普遍性による経路。

## 規約

元の環の p 正則性や有界ねじれは要求せず、全冪商の g 正則性だけを仮定する。

## 使われ方

モニック無限根入力に適用して、原典の完備多項式商を既存の完備入力へ接続する。
-/

@[expose] public noncomputable section PrimeAdicCompletionQuotientExchange

namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R] (p : ℕ) (g : R)
local notation "C" => AdicCompletion (Ideal.span {(p : R)}) R
local notation "j" => algebraMap R C
local notation "S" => R ⧸ Ideal.span {(g : R)}
local notation "q" => Ideal.Quotient.mk (Ideal.span {(g : R)})
local notation "CS" => AdicCompletion (Ideal.span {(p : S)}) S
local notation "jS" => algebraMap S CS
local notation "Z" => C ⧸ Ideal.span {j g}
local notation "qC" => Ideal.Quotient.mk (Ideal.span {j g})
variable (hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {(p : R) ^ n})
  (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) g))

include hg in
/-- 概要：全冪商で正則な主関係は p 完備化と係数射を保って交換する。
方針：両側の完備性と二つの普遍性で往復射を作り、その合成を元の環上で確認する。
規約：元の主商と通常の p 完備化を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力環の同定。 -/
theorem exists_primeAdicCompletionQuotientEquiv :
    ∃ e : Z ≃+* CS, e.toRingHom.comp ((qC).comp j) = (jS).comp q := by
  let := primeAdicCompletion_isAdicComplete S p
  let := primeAdicCompletion_principal_quotient_isAdicComplete R p g hg
  obtain ⟨F₀, hF₀, _⟩ := existsUnique_primeAdicCompletionHom R p ((jS).comp q)
  have hF₀g : F₀ (j g) = 0 := by
    have h := RingHom.congr_fun hF₀ g
    simpa only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self g), map_zero] using h
  let F : Z →+* CS := Ideal.Quotient.lift _ F₀ (by
    change Ideal.span {j g} ≤ RingHom.ker F₀
    exact Ideal.span_le.mpr (fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hF₀g))
  let r : S →+* Z := Ideal.Quotient.lift _ ((qC).comp j) (by
    change Ideal.span {(g : R)} ≤ RingHom.ker ((qC).comp j)
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  obtain ⟨G, hG, _⟩ := existsUnique_primeAdicCompletionHom S p r
  have hGF : G.comp F = RingHom.id Z := by
    apply Ideal.Quotient.ringHom_ext
    apply primeAdicCompletion_ringHom_ext R p
    apply RingHom.ext
    intro x
    change G (F₀ (j x)) = qC (j x)
    rw [show F₀ (j x) = jS (q x) from RingHom.congr_fun hF₀ x]
    exact RingHom.congr_fun hG (q x)
  have hFG : F.comp G = RingHom.id CS := by
    apply primeAdicCompletion_ringHom_ext S p
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change F (G (jS (q a))) = jS (q a)
    rw [show G (jS (q a)) = r (q a) from RingHom.congr_fun hG (q a)]
    exact RingHom.congr_fun hF₀ a
  let e : Z ≃+* CS := { F with
    invFun := G
    left_inv := RingHom.congr_fun hGF
    right_inv := RingHom.congr_fun hFG }
  refine ⟨e, ?_⟩
  apply RingHom.ext
  exact RingHom.congr_fun hF₀

/-- 概要：全冪商で正則な主関係と p 完備化を交換する具体的な環同型。
方針：係数射を保つ同型の存在定理から一つ選ぶ。
規約：後続の係数公式で選択に依存しない入力作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力の比較射。 -/
def primeAdicCompletionQuotientEquiv : Z ≃+* CS :=
  (exists_primeAdicCompletionQuotientEquiv R p g hg).choose

/-- 概要：完備化と主商の交換同型は元の全係数元を保つ。
方針：選んだ同型が満たす環射の合成等式を各元に適用する。
規約：根変数の像を含め、元の環全体で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力根の作用を追跡する。 -/
theorem primeAdicCompletionQuotientEquiv_coeff (x : R) :
    primeAdicCompletionQuotientEquiv R p g hg (qC (j x)) = jS (q x) :=
  RingHom.congr_fun (exists_primeAdicCompletionQuotientEquiv R p g hg).choose_spec x

end SerrePositivity.BhattScholze.Andre

end PrimeAdicCompletionQuotientExchange
