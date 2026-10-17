module

public import SerrePositivity.BhattScholze.RankOneDPAnyBasis
public import SerrePositivity.BhattScholze.PrincipalDPPresentation

/-!
# André E1・E2：係数環同型に沿う一元分冪表示の移送

## 概要

係数環同型 A≃B は自由一元分冪代数と γ₁=y の一次関係商の環同型を誘導する。
標準係数・全標準生成元を保つ。BS Rem 7.15(1)（著者版 p.62）の係数比較への準備。

## 方針

既存の分冪代数の係数変更射を実環射として束ね、単項式基底で逆合成を確認する。
一次関係の生成イデアルを照合して実商同型へ降ろす。

## 規約

係数環の標数・正則性・非零性を要求しない。分冪構造の存在はこの通常環同型と別に扱う。

## 使われ方

無限根環の実 mod p 商と、係数商上の無限根環の間で実 pd 包の台環を移す。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 概要：自由一元分冪代数の環射は係数と γₙ(1) の値で決まる。
方針：一方の係数射から終域に A 作用を与え、標準分冪基底上の線形外延性を使う。
規約：終域に事前の A 代数構造を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数同型による逆合成の検証。 -/
theorem rankOneDPRingHom_ext {T : Type w} [CommRing T]
    (f g : DividedPowerAlgebra A A →+* T)
    (hc : ∀ a, f (algebraMap A _ a) = g (algebraMap A _ a))
    (hγ : ∀ n, f (DividedPowerAlgebra.dp A n (1 : A)) =
      g (DividedPowerAlgebra.dp A n (1 : A))) : f = g := by
  let : Algebra A T := (f.comp (algebraMap A (DividedPowerAlgebra A A))).toAlgebra
  let ff : DividedPowerAlgebra A A →ₐ[A] T := { f with commutes' := fun _ => rfl }
  let gg : DividedPowerAlgebra A A →ₐ[A] T := { g with commutes' := fun a => (hc a).symm }
  have he : ff = gg := by
    apply AlgHom.toLinearMap_injective
    apply (rankOneDPAnyBasis A).ext
    intro n
    simpa only [AlgHom.toLinearMap_apply, rankOneDPAnyBasis_apply, ff, gg, AlgHom.coe_mk] using hγ n
  exact congrArg AlgHom.toRingHom he

/-- 概要：任意の係数環射は自由一元分冪代数の実環射を誘導する。
方針：係数環射の指定する代数構造を局所導入して既存の分冪代数写像を使う。
規約：元の台環と係数作用は変更しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更の具体的な環射。 -/
def rankOneDPRingMap (φ : A →+* B) : DividedPowerAlgebra A A →+* DividedPowerAlgebra B B := by
  letI := φ.toAlgebra
  exact (DividedPowerAlgebra.map B (Algebra.linearMap A B)).toRingHom

/-- 概要：誘導された環射は標準係数を元の係数環射で送る。
方針：分冪代数の係数代数射の可換性を使う。
規約：終域の自然な B 係数射で値を述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示関係の係数の照合。 -/
theorem rankOneDPRingMap_coeff (φ : A →+* B) (a : A) :
    rankOneDPRingMap φ (algebraMap A _ a) = algebraMap B _ (φ a) := by
  let := φ.toAlgebra
  exact (DividedPowerAlgebra.map B (Algebra.linearMap A B)).commutes a

/-- 概要：誘導環射は標準分冪 γₙ(1) を同じ次数の標準分冪へ送る。
方針：分冪代数写像の生成元公式と係数射の単位保存を使う。
規約：全ての次数 n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示関係と標準生成元の照合。 -/
theorem rankOneDPRingMap_dp (φ : A →+* B) (n : ℕ) :
    rankOneDPRingMap φ (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) := by
  let := φ.toAlgebra
  change DividedPowerAlgebra.map B (Algebra.linearMap A B)
    (DividedPowerAlgebra.dp A n (1 : A)) = _
  rw [DividedPowerAlgebra.map_apply_dp, Algebra.linearMap_apply, map_one]

/-- 概要：係数環同型は自由一元分冪代数の環同型を誘導する。
方針：正逆の係数変更射の合成を係数と標準基底上で確認する。
規約：標数や非零性の仮定は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係商の同型の構成。 -/
def rankOneDPRingEquiv (e : A ≃+* B) : DividedPowerAlgebra A A ≃+* DividedPowerAlgebra B B :=
  RingEquiv.ofRingHom (rankOneDPRingMap e.toRingHom) (rankOneDPRingMap e.symm.toRingHom)
    (by
      apply rankOneDPRingHom_ext
      · intro b
        simp only [RingHom.comp_apply, rankOneDPRingMap_coeff, RingHom.id_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      · intro n
        simp only [RingHom.comp_apply, rankOneDPRingMap_dp, RingHom.id_apply])
    (by
      apply rankOneDPRingHom_ext
      · intro a
        simp only [RingHom.comp_apply, rankOneDPRingMap_coeff, RingHom.id_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      · intro n
        simp only [RingHom.comp_apply, rankOneDPRingMap_dp, RingHom.id_apply])

/-- 概要：自由分冪の係数同型は標準係数を対応させる。
方針：同型の順射の係数公式を使う。
規約：実係数射の値として述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係イデアルの比較。 -/
theorem rankOneDPRingEquiv_coeff (e : A ≃+* B) (a : A) :
    rankOneDPRingEquiv e (algebraMap A _ a) = algebraMap B _ (e a) :=
  rankOneDPRingMap_coeff e.toRingHom a

/-- 概要：自由分冪の係数同型は標準分冪の次数を保つ。
方針：同型の順射の生成元公式を使う。
規約：全ての n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の標準生成元の比較。 -/
theorem rankOneDPRingEquiv_dp (e : A ≃+* B) (n : ℕ) :
    rankOneDPRingEquiv e (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) :=
  rankOneDPRingMap_dp e.toRingHom n

/-- 概要：一次関係イデアルは係数同型で対応する一次関係イデアルへ移る。
方針：生成元 γ₁(1)-y の像を係数と分冪の公式で計算する。
規約：入力 y の正則性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実商同型の入力。 -/
theorem principalDPRelationIdeal_map_ringEquiv (e : A ≃+* B) (y : A) :
    principalDPRelationIdeal (e y) =
      (principalDPRelationIdeal y).map (rankOneDPRingEquiv e).toRingHom := by
  rw [principalDPRelationIdeal, principalDPRelationIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  change DividedPowerAlgebra.dp B 1 (1 : B) - algebraMap B _ (e y) =
    rankOneDPRingMap e.toRingHom (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y)
  rw [map_sub, rankOneDPRingMap_dp, rankOneDPRingMap_coeff]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- 概要：係数環同型は γ₁=y の一次関係商の実環同型を誘導する。
方針：自由分冪代数の同型と一次関係イデアルの像の計算を商同型に渡す。
規約：これは通常環同型であり、分冪構造は別途移す。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商上の pd 包への移送。 -/
def principalDPRingEquiv (e : A ≃+* B) (y : A) :
    PrincipalDPPresentation A y ≃+* PrincipalDPPresentation B (e y) :=
  Ideal.quotientEquiv _ _ (rankOneDPRingEquiv e) (principalDPRelationIdeal_map_ringEquiv e y)

/-- 概要：一次関係商の係数同型は元の係数を対応させる。
方針：商同型の代表元公式と自由分冪同型の係数公式を使う。
規約：標準係数射をそのまま使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数上の互換性。 -/
theorem principalDPRingEquiv_coeff (e : A ≃+* B) (y a : A) :
    principalDPRingEquiv e y (algebraMap A _ a) = algebraMap B _ (e a) := by
  change principalDPRingEquiv e y (Ideal.Quotient.mk _ (algebraMap A _ a)) = _
  rw [principalDPRingEquiv, Ideal.quotientEquiv_mk, rankOneDPRingEquiv_coeff]
  rfl

/-- 概要：一次関係商の係数同型は標準生成元を同じ次数の標準生成元へ送る。
方針：商同型の代表元公式と自由分冪の生成元公式を使う。
規約：入力元は係数同型で送る。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の標準値の移送。 -/
theorem principalDPRingEquiv_generator (e : A ≃+* B) (y : A) (n : ℕ) :
    principalDPRingEquiv e y (principalDPGenerator y n) = principalDPGenerator (e y) n := by
  change principalDPRingEquiv e y (Ideal.Quotient.mk _ (DividedPowerAlgebra.dp A n (1 : A))) = _
  rw [principalDPRingEquiv, Ideal.quotientEquiv_mk, rankOneDPRingEquiv_dp]
  rfl


/-- 概要：係数同型が入力 y を指定した z へ送れば、それらの一次関係商は環同型。
方針：入力の等式で標準の係数同型比較を移す。
規約：入力の像の等式を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の異なる具体的な剰余表示の同定。 -/
def principalDPRingEquivOfEq (e : A ≃+* B) (y : A) (z : B) (hy : e y = z) :
    PrincipalDPPresentation A y ≃+* PrincipalDPPresentation B z := by
  subst z
  exact principalDPRingEquiv e y

/-- 概要：入力像の等式を使った商同型も元の係数を係数同型で送る。
方針：入力像の等式で標準の係数公式へ帰着する。
規約：係数環射の値を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の移送した分冪構造の入力値。 -/
theorem principalDPRingEquivOfEq_coeff (e : A ≃+* B) (y : A) (z : B) (hy : e y = z) (a : A) :
    principalDPRingEquivOfEq e y z hy (algebraMap A _ a) = algebraMap B _ (e a) := by
  subst z
  exact principalDPRingEquiv_coeff e y a

/-- 概要：入力像の等式を使った商同型は全標準生成元を同じ次数へ送る。
方針：入力像の等式で標準の生成元公式へ帰着する。
規約：全ての n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数イデアルと分冪値の比較。 -/
theorem principalDPRingEquivOfEq_generator (e : A ≃+* B) (y : A) (z : B) (hy : e y = z) (n : ℕ) :
    principalDPRingEquivOfEq e y z hy (principalDPGenerator y n) = principalDPGenerator z n := by
  subst z
  exact principalDPRingEquiv_generator e y n

end SerrePositivity.BhattScholze.Andre
