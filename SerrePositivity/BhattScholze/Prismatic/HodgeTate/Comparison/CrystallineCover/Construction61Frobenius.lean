module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.Frobenius.PrincipalQuotientFlat
public import SerrePositivity.BhattScholze.Prism.Basic.UniversalOrientedFrobenius
public import SerrePositivity.BhattScholze.Prism.Basic.GeneratorRegularity

/-!
# Construction 6.1 の Frobenius 入力

## 概要
原典の平坦性の仮定と Construction 6.1 の完全平坦性の入力を、式 (6) の忠実平坦な射に接続する。

## 方針
mod p の Frobenius は p 乗なので、主元剰余の一般の忠実平坦性を適用する。

## 規約
BS 著者版 Construction 6.1 と Example 3.4。普遍 prism には通常の平坦性を仮定しない。

## 使われ方
結晶被覆の剰余の分解、Tor 振幅と保存性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic.Construction61

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：δ 環の Frobenius の mod p は p 乗。
方針：代表元を取り、φ(a)=a^p+pδ(a) を還元する。
規約：BS 著者版 Construction 6.1 の式 (6)。
使われ方：主元剰余の Frobenius 射の指定。 -/
theorem modPFrobenius_apply (a : ModP A p) :
    modPMap p P.deltaStructure.frobeniusLift a = a ^ p := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk _ (P.deltaStructure.frobeniusLift a) = _
  rw [P.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
  have hp : (p : ModP A p) = 0 := by
    simpa only [map_natCast] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A)))
  rw [hp, zero_mul, add_zero]

/-- 概要：原典の通常の平坦性の仮定から Construction 6.1 の入力が出る。
方針：平坦な加群は任意のイデアルについて完全平坦。
規約：BS 著者版 Construction 6.1 の仮定を弱い入力へ送る。
使われ方：原典どおりの仮定を持つ場合の接続。 -/
theorem completelyFlat_of_flat
    (hF : (modPMap p P.deltaStructure.frobeniusLift).Flat) :
    IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)) :=
  RingHom.completelyFlat_scalarModule_of_flat _ hF _

/-- Construction 6.1 の式 (6) の中央の射。 -/
abbrev residueFrobenius :
    (ModP A p ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator}) →+*
      (ModP A p ⧸ Ideal.span
        {(Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator) ^ p}) :=
  Frobenius.principalQuotientMap (modPMap p P.deltaStructure.frobeniusLift)
    (modPFrobenius_apply P) _

/-- 概要：d 完全平坦性から式 (6) の中央の忠実平坦性を得る。
方針：主元剰余の一般の Frobenius 判定を使う。
規約：BS 著者版 Construction 6.1、Construction 6.1 の明示的な入力。
使われ方：結晶被覆による消滅の検出。 -/
theorem residueFrobenius_faithfullyFlat
    (hF : IsCompletelyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift))) :
    (residueFrobenius P).FaithfullyFlat :=
  Frobenius.principalQuotientMap_faithfullyFlat _ _ _ hF

/-- 概要：A/d の p 正則性から d の mod p 正則性を得る。
方針：既存の二元の正則性の交換を適用する。
規約：BS 著者版 Construction 6.1 の最初の剰余射。
使われ方：一元 Koszul 分解による Tor 次元の評価。 -/
theorem generator_modP_regular
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsSMulRegular (ModP A p)
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator) :=
  Andre.perfectPrism_generator_modPrime_regular P hR

/-- 概要：普遍 prism の式 (6) の中央の射は忠実平坦。
方針：普遍向き付き prism の d 完全平坦性を直接入力する。
規約：BS 著者版 Example 3.4、Construction 6.1、Construction 6.1。
使われ方：普遍的な結晶被覆の保存性。 -/
theorem universal_residueFrobenius_faithfullyFlat :
    (residueFrobenius (universalOrientedPrism.{u} p)).FaithfullyFlat :=
  residueFrobenius_faithfullyFlat _ (universalOrientedPrism_frobenius_isCompletelyFlat p)

/-- 概要：普遍 prism の生成元は mod p で正則。
方針：普遍向き付き prism の A/d の p 正則性を直接入力する。
規約：BS 著者版 Example 3.4、Construction 6.1、Construction 6.1。
使われ方：普遍的な被覆の Tor 振幅。 -/
theorem universal_generator_modP_regular :
    IsSMulRegular (ModP (UniversalOrientedPrismRing.{u} p) p)
      (Ideal.Quotient.mk (Ideal.span {(p : UniversalOrientedPrismRing.{u} p)})
        (universalOrientedPrism.{u} p).generator) :=
  generator_modP_regular _ (universalOrientedPrism_mod_generator_p_regular p)

end SerrePositivity.BhattScholze.Prismatic.Construction61

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 6.1" (partial := component) "BS-W17 H1・H2（11-11）：被覆 B と α、式 (6)、(1) 保存性と (2) 有限 Tor 振幅（上界 3）を上に有界でない複体で本体に。D77：原典の「Frobenius が平坦」の代わりに d 完全平坦性を入力（普遍の場合は K2）。(3) Lemma 4.20 は G10 の後"] _root_.SerrePositivity.BhattScholze.Prismatic.Construction61.completelyFlat_of_flat
