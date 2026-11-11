module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction

/-!
# テンソル積の片側で消える関係を係数環にも入れる比較

## 概要
左因子の剰余で零になる基底の関係は、右因子と共通基底を割ってもテンソル積を変えない。
## 方針
通常のテンソル商比較と、全射な基底変更の両立するスカラー作用を使う。
## 規約
平坦性や正則性を仮定しない。実際の通常環の同型。
## 使われ方
BS 著者版 Example 7.9 の包絡剰余を、関係商上の完備テンソルへ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable (R A E : Type u) [CommRing R] [CommRing A] [CommRing E]
  [Algebra R A] [Algebra R E]
variable (I : Ideal R) (J : Ideal E) (hIJ : I.map (algebraMap R E) ≤ J)

/-- 左因子の指定剰余への関係商の作用。 -/
def quotientFactorAlgebra : Algebra (R ⧸ I) (E ⧸ J) :=
  (Ideal.quotientMap J (algebraMap R E) (Ideal.map_le_iff_le_comap.mp hIJ)).toAlgebra

/-- 片側で消える基底の関係を右側と共通基底へ移す、単位を保つ通常環の比較。 -/
def tensorQuotientFactorEquiv :
    letI := quotientFactorAlgebra R E I J hIJ
    letI := adicQuotientAlgebra I A
    ((E ⊗[R] A) ⧸ J.map (algebraMap E (E ⊗[R] A))) ≃+*
      ((A ⧸ I.map (algebraMap R A)) ⊗[R ⧸ I] (E ⧸ J)) := by
  let K := I.map (algebraMap R A)
  let EA := E ⧸ J
  let AA := A ⧸ K
  letI := quotientFactorAlgebra R E I J hIJ
  letI := adicQuotientAlgebra I A
  letI : IsScalarTower R (R ⧸ I) EA := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R (R ⧸ I) AA := IsScalarTower.of_algebraMap_eq' rfl
  let W := EA ⊗[R] A
  let ι : A →+* W := Algebra.TensorProduct.includeRight.toRingHom
  have hk : K.map ι = ⊥ := by
    apply le_antisymm _ bot_le
    change (I.map (algebraMap R A)).map ι ≤ ⊥
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    change ι (algebraMap R A x) = 0
    change (1 : EA) ⊗ₜ[R] (algebraMap R A x) = 0
    have hzero : algebraMap R EA x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ (Ideal.mem_map_of_mem _ hx))
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul x, hzero, TensorProduct.zero_tmul]
  let e1 := (Algebra.TensorProduct.quotientTensorEquiv (R := R) E A E J).symm.toRingEquiv
  let e2 := (Algebra.TensorProduct.tensorQuotientEquiv (R := R) EA A EA K).toRingEquiv.trans
    ((Ideal.quotEquivOfEq hk).trans (RingEquiv.quotientBot W))
  letI : TensorProduct.CompatibleSMul R (R ⧸ I) EA AA :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ Ideal.Quotient.mk_surjective
  let e3 := (Algebra.TensorProduct.equivOfCompatibleSMul R (R ⧸ I) EA EA AA).symm.toRingEquiv
  exact e1.trans (e2.symm.trans (e3.trans (Algebra.TensorProduct.comm (R ⧸ I) EA AA).toRingEquiv))

/-- 比較は、通常テンソル積の二つの係数射を指定された商の係数射へ送る。 -/
theorem tensorQuotientFactorEquiv_tmul (e : E) (a : A) :
    letI := quotientFactorAlgebra R E I J hIJ
    letI := adicQuotientAlgebra I A
    tensorQuotientFactorEquiv R A E I J hIJ (Ideal.Quotient.mk _ (e ⊗ₜ[R] a)) =
      Ideal.Quotient.mk _ a ⊗ₜ[R ⧸ I] Ideal.Quotient.mk J e := by
  simp [tensorQuotientFactorEquiv, Algebra.TensorProduct.equivOfCompatibleSMul,
    TensorProduct.equivOfCompatibleSMul, Algebra.TensorProduct.mapOfCompatibleSMul,
    RingEquiv.quotientBot, Ideal.quotEquivOfEq_mk]
  erw [Ideal.quotEquivOfEq_mk]
  erw [Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul (R := R)
    (E ⧸ J) A (E ⧸ J) (I.map (algebraMap R A)) (Ideal.Quotient.mk J e) a]
  rfl

end SerrePositivity
