module

public import SerrePositivity.BhattScholze.Andre.Remark715.DistinguishedWittDenominator

/-!
# André E1・E2：分母正規化単元の零環を含む自然性

## 概要

p=0 の任意の係数商で分母正規化単元を作り、通常環射での自然性を示す。
BS Rem 7.15（著者版 p.62）の二つの raw 剰余の逆比較に用いる。

## 方針

非零環では既存の Witt 単元を使い、零環では全 Witt 元の一致を使う。
値は係数を一段ずらす具体式なので通常環射で保たれる。

## 規約

標数が正確に p であることや非零環であることを商に要求しない。

## 使われ方

剰余比較の両逆合成で、単元とその逆元の像を照合する。
-/

@[expose] public noncomputable section
universe u
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
使われ方：BS Rem 7.15（著者版 p.62）の任意の raw 剰余での分母変換。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余の変数変換。 -/
def distinguishedWittResidueUnit (hpB : (p : B) = 0) : (WittVector p B)ˣ :=
  (distinguishedWittDenominator_isUnit_of_prime_zero D hpA q d hd hpB).unit

/-- 概要：零環を含む正規化単元の値は具体的な係数ずらし。
方針：選んだ単元の仕様を使う。
規約：非零性の分岐に依存しない値の等式。
使われ方：BS Rem 7.15（著者版 p.62）の通常環射での自然性。 -/
theorem distinguishedWittResidueUnit_val (hpB : (p : B) = 0) :
    (distinguishedWittResidueUnit D hpA q d hd hpB : WittVector p B) =
      deltaPDivisionWittResidueSolution D q d :=
  (distinguishedWittDenominator_isUnit_of_prime_zero D hpA q d hd hpB).unit_spec

/-- 概要：p が零の任意の係数商で φ(d) の Witt 像は p の単元倍。
方針：単元の値を具体的 Witt 解へ戻して除算公式を使う。
規約：q(d)=0 と源 ghost 射の単射性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 分母の置き換え。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の比較射の逆合成。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の逆元の自然性への入力。 -/
theorem distinguishedWittResidueUnit_map_units (hpB : (p : B) = 0)
    (q' : A →+* C) (hpC : (p : C) = 0) (F : B →+* C) (hF : F.comp q = q') :
    Units.map (WittVector.map F).toMonoidHom (distinguishedWittResidueUnit D hpA q d hd hpB) =
      distinguishedWittResidueUnit D hpA q' d hd hpC := by
  apply Units.ext
  exact distinguishedWittResidueUnit_map D hpA q d hd hpB q' hpC F hF

/-- 概要：正規化単元の逆元の値も通常環射で保たれる。
方針：単元群の写像が逆元を保つことを使う。
規約：逆元は単元群で取り、その値を Witt 環へ送る。
使われ方：BS Rem 7.15（著者版 p.62）の変数変換の両逆合成。 -/
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
