module

public import SerrePositivity.BhattScholze.PDCompletionInterface

/-!
# André E1・E2：両座標を殺す商と実導来完備化 H⁰

## 概要

p,d を含むイデアル I に対し、実導来 (p,d) 完備化 H⁰ の I の像による商は A/I と環同型。
BS Rem 7.15（著者版 p.62）の完備化後の剰余を具体的な未完備の剰余へ戻す比較。

## 方針

商では p,d が零なので、標準商射を実 H⁰ の環普遍性で延長する。
係数からの逆射を作り、逆合成を商の普遍性と実完備化の一意性で確認する。

## 規約

実際の H⁰ と標準単位を用いる。p,d の正則性・Noether 性を仮定しない。

## 使われ方

Frobenius 側の実完備化の (p,d) 商を、raw 包の同じ剰余へ同定する。
-/

@[expose] public noncomputable section
universe u
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
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の剰余比較の逆射。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の商比較の構成。 -/
def pdCompletionKilledCoordinateMap :
    letI := pdCompletionCommRing A p d
    H →+* A ⧸ I := by
  let := pdCompletionCommRing A p d
  exact (existsUnique_pdCompletionKilledCoordinateMap p d I hpI hdI).choose

/-- 概要：選択した延長は標準完備化単位との合成で元の商射になる。
方針：選択した射の仕様を使う。
規約：環射の合成の等式。
使われ方：BS Rem 7.15（著者版 p.62）の係数上の逆合成。 -/
theorem pdCompletionKilledCoordinateMap_comp_unit :
    letI := pdCompletionCommRing A p d
    (pdCompletionKilledCoordinateMap p d I hpI hdI).comp uA = Ideal.Quotient.mk I := by
  let := pdCompletionCommRing A p d
  exact (existsUnique_pdCompletionKilledCoordinateMap p d I hpI hdI).choose_spec.1

/-- 概要：標準延長は各係数元の完備化像を同じ商代表元へ送る。
方針：標準単位との合成公式を各元で評価する。
規約：元の商射の値を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の代表元での剰余比較。 -/
theorem pdCompletionKilledCoordinateMap_unit (b : A) :
    letI := pdCompletionCommRing A p d
    pdCompletionKilledCoordinateMap p d I hpI hdI (uA b) = Ideal.Quotient.mk I b := by
  let := pdCompletionCommRing A p d
  exact RingHom.congr_fun (pdCompletionKilledCoordinateMap_comp_unit p d I hpI hdI) b

/-- 概要：元の係数商から実完備化の像イデアル商への標準環射。
方針：I の係数像がその像イデアルに属することから商へ降ろす。
規約：p,d を含むことは順射自体には不要。
使われ方：BS Rem 7.15（著者版 p.62）の剰余比較の順射。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の実係数射の照合。 -/
theorem pdCompletionQuotientFromRaw_mk (b : A) :
    letI := pdCompletionCommRing A p d
    pdCompletionQuotientFromRaw p d I (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk J (uA b) := rfl

/-- 概要：実完備化の像イデアル商から元の商への逆射。
方針：標準延長が I の全ての像を殺すことを使う。
規約：像イデアル全体を殺すことを商の普遍性へ渡す。
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の剰余比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の一意性による逆合成。 -/
theorem pdCompletionQuotientToRaw_mk (t : H) :
    letI := pdCompletionCommRing A p d
    pdCompletionQuotientToRaw p d I hpI hdI (Ideal.Quotient.mk J t) =
      pdCompletionKilledCoordinateMap p d I hpI hdI t := rfl

/-- 概要：元の商から完備化の商へ送り戻す合成は恒等射。
方針：元の環の代表元で標準延長の係数公式を使う。
規約：商射の全射性による外延性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の剰余環同型の片側逆。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の剰余環同型のもう片側逆。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の剰余を raw 剰余へ戻す同型。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の pd 包への係数を保つ接続。 -/
theorem pdCompletionQuotientEquivOfKilledCoordinates_unit (b : A) :
    letI := pdCompletionCommRing A p d
    pdCompletionQuotientEquivOfKilledCoordinates p d I hpI hdI
      (Ideal.Quotient.mk J (uA b)) = Ideal.Quotient.mk I b := by
  let := pdCompletionCommRing A p d
  exact RingHom.congr_fun (pdCompletionKilledCoordinateMap_comp_unit p d I hpI hdI) b

end SerrePositivity.BhattScholze.Andre
