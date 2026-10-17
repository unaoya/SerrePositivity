module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.PDBaseChange

/-!
# BS Rem 7.15（著者版 p.62）：R/p から R/ϖ への pd 底変換

## 概要
実装の A/p 表示との比較とは別に、R/p 上の無限根 pd 表示を R/ϖ へ底変換する。

## 方針
一般の係数商と係数環同型を組み合わせ、(R/p)/(ϖ)≃R/ϖ を使う。

## 規約
通常表示環の同型なのでモニック性・正則性は不要。実分冪射は PDCompatibility に置く。

## 使われ方
原典の R/ϖ⊗_{R/p} という係数表記を実際のテンソル積型として供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 概要：係数環同型は無限根環での多項式評価と可換。
方針：係数単項式と標準変数の像を照合する。
規約：指数モノイドは変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の二重商係数の移送。 -/
theorem rootCoefficientChange_baseMap {S B : Type u} [CommRing S] [CommRing B]
    (p : ℕ) (hp : 0 < p) (e : S ≃+* B) (f : Polynomial S) :
    AddMonoidAlgebra.mapRingEquiv (powerRootExponentMonoid p hp) e
      (powerRootPolynomialBaseMap S p hp f) =
        powerRootPolynomialBaseMap B p hp (f.map e.toRingHom) := by
  simp only [powerRootPolynomialBaseMap, Polynomial.aeval_def, Polynomial.eval₂_map]
  change (AddMonoidAlgebra.mapRingEquiv (powerRootExponentMonoid p hp) e).toRingHom
    (Polynomial.eval₂ (algebraMap S (PowerRootPolynomial S p hp))
      (powerRootPolynomialVariable S p hp 0) f) = _
  rw [Polynomial.hom_eval₂]
  have hv : AddMonoidAlgebra.mapRingEquiv (powerRootExponentMonoid p hp) e
      (powerRootPolynomialVariable S p hp 0) = powerRootPolynomialVariable B p hp 0 := by
    simp only [powerRootPolynomialVariable, AddMonoidAlgebra.mapRingEquiv_single, map_one]
  change Polynomial.eval₂ _
    (AddMonoidAlgebra.mapRingEquiv (powerRootExponentMonoid p hp) e
      (powerRootPolynomialVariable S p hp 0)) f = _
  rw [hv]
  congr 1
  apply RingHom.ext
  intro s
  change AddMonoidAlgebra.mapRingEquiv (powerRootExponentMonoid p hp) e
    (algebraMap S (PowerRootPolynomial S p hp) s) =
      algebraMap B (PowerRootPolynomial B p hp) (e s)
  simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapRingEquiv_single]

section Change
variable (S B : Type u) [CommRing S] [CommRing B] (c : S)
variable (e : (S ⧸ Ideal.span {c}) ≃+* B)

/-- 概要：指定係数商同型による自然な係数代数構造。
方針：標準商射と同型を合成する。規約：作用を明示的に固定する。
使われ方：BS Rem 7.15（著者版 p.62）の原典係数でのテンソル型。 -/
@[instance_reducible] def quotientCoefficientAlgebra : Algebra S B :=
  (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {c}))).toAlgebra

/-- 概要：係数商同型を指定作用上の代数同型として扱う。
方針：係数作用の定義を展開する。規約：同型は元の環同型と同じ。
使われ方：BS Rem 7.15（著者版 p.62）のテンソル因子の変更。 -/
def quotientCoefficientAlgEquiv :
    let := quotientCoefficientAlgebra S B c e
    (S ⧸ Ideal.span {c}) ≃ₐ[S] B := by
  let := quotientCoefficientAlgebra S B c e
  exact { e with commutes' := fun _ => rfl }

/-- 概要：係数商と係数同型の合成に沿う無限根 pd 表示の実テンソル同型。
方針：一般の係数商底変換と、入力評価を保つ係数環同型を合成する。
規約：入力多項式は元の S から指定した係数射で移す。
使われ方：BS Rem 7.15（著者版 p.62）の R/p と R/ϖ の直接比較。 -/
def powerRootPDTensorChangeEquiv (p : ℕ) (hp : 0 < p) (f : Polynomial S) :
    let := quotientCoefficientAlgebra S B c e
    B ⊗[S] PrincipalDPPresentation (PowerRootPolynomial S p hp)
      (powerRootPolynomialBaseMap S p hp f) ≃+*
        PrincipalDPPresentation (PowerRootPolynomial B p hp)
          (powerRootPolynomialBaseMap B p hp
            (f.map (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {c}))))) := by
  let := quotientCoefficientAlgebra S B c e
  let D := PrincipalDPPresentation (PowerRootPolynomial S p hp)
    (powerRootPolynomialBaseMap S p hp f)
  refine ((Algebra.TensorProduct.congr (quotientCoefficientAlgEquiv S B c e).symm
    (AlgEquiv.refl : D ≃ₐ[S] D)).toRingEquiv.trans
      (powerRootPDTensorQuotientEquiv S p hp c f)).trans ?_
  refine principalDPRingEquivOfEq
    (AddMonoidAlgebra.mapRingEquiv (powerRootExponentMonoid p hp) e) _ _ ?_
  rw [rootCoefficientChange_baseMap, Polynomial.map_map]
end Change

/-- 概要：R/p の pd 表示を原典の R/ϖ へテンソルすると、同じ f の R/ϖ pd 表示となる。
方針：(ϖ^p)=(p) による二重商同型を一般の係数テンソル比較へ渡す。
規約：R は任意の可換環でよく、入力 f のモニック性は環同型には不要。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ⊗_{R/p} による係数表記の照合。 -/
def primePDTensorVarpiEquiv {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p)
    (v : R) (hspan : Ideal.span {v ^ p} = Ideal.span {(p : R)}) (f : Polynomial R) :
    let e := primeVarpiDoubleQuotientEquiv v (p : R) p hp hspan
    let := quotientCoefficientAlgebra (R ⧸ Ideal.span {(p : R)}) (R ⧸ Ideal.span {v})
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) v) e
    (R ⧸ Ideal.span {v}) ⊗[R ⧸ Ideal.span {(p : R)}]
      PrincipalDPPresentation (PowerRootPolynomial (R ⧸ Ideal.span {(p : R)}) p hp)
        (powerRootPolynomialBaseMap (R ⧸ Ideal.span {(p : R)}) p hp
          (f.map (Ideal.Quotient.mk (Ideal.span {(p : R)})))) ≃+*
      PrincipalDPPresentation (PowerRootPolynomial (R ⧸ Ideal.span {v}) p hp)
        (powerRootPolynomialBaseMap (R ⧸ Ideal.span {v}) p hp
          (f.map (Ideal.Quotient.mk (Ideal.span {v})))) := by
  let e := primeVarpiDoubleQuotientEquiv v (p : R) p hp hspan
  let := quotientCoefficientAlgebra (R ⧸ Ideal.span {(p : R)}) (R ⧸ Ideal.span {v})
    (Ideal.Quotient.mk (Ideal.span {(p : R)}) v) e
  have hcoeff : (e.toRingHom.comp (Ideal.Quotient.mk _)).comp
      (Ideal.Quotient.mk (Ideal.span {(p : R)})) = Ideal.Quotient.mk (Ideal.span {v}) := by
    ext r
    rfl
  have h := powerRootPDTensorChangeEquiv (R ⧸ Ideal.span {(p : R)}) (R ⧸ Ideal.span {v})
    (Ideal.Quotient.mk (Ideal.span {(p : R)}) v) e p hp
    (f.map (Ideal.Quotient.mk (Ideal.span {(p : R)})))
  rw [Polynomial.map_map, hcoeff] at h
  exact h

end SerrePositivity.BhattScholze.Andre.VarpiComparison
