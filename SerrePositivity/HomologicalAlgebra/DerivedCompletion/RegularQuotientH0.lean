module

public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction

/-!
# 離散な導来対象の正則剰余と零次

## 概要
離散な導来対象の正則主元剰余の H⁰ を、元の H⁰ の通常商に同定する。
この比較は商のねじれの上界を環の模型へ移す。

## 方針
正規化された零次同型と、標準導来剰余の augmentation を使う。

## 規約
元の係数環とその商に関する線形性を保持する。

## 使われ方
BS 著者版 Example 7.9 の包絡候補の有界性。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.DerivedCompletion

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

variable {E H : Type u} [CommRing E] [CommRing H]

/-- 概要：離散な対象と H⁰ に正則な主元の導来剰余は、通常の H⁰ の剰余を持つ。
方針：正規化された single 比較に沿って標準剰余の同型を移す。
規約：同型は E/(d) 線形である。
使われ方：完備源の剰余のねじれ評価を零次の通常商へ移す。 -/
def pureRegularQuotientH0Iso (d : E) (hd : IsSMulRegular E d)
    (X : DerivedCategory.Minus (ModuleCat.{u} E))
    (hge : X.obj.IsGE 0) (hle : X.obj.IsLE 0)
    (hreg : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj) d) :
    (DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj ≅
      (quotientModuleFunctor (Ideal.span {d})).obj
        ((DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj) := by
  let := hge
  let := hle
  let M := (DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj
  let eX : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj 0)
  let eQ := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).mapIso eX ≪≫
    derivedQuotientModuleIsoOfRegular d hd M hreg
  exact (DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso eQ) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat (E ⧸ Ideal.span {d})) 0).app _

/-- 概要：離散な正則対象の剰余の有界 p ねじれは、係数線形な零次環模型の剰余へ移る。
方針：正則剰余の H⁰ 同型、加群商の関手性、通常の代数商との比較を合成する。
規約：ねじれの共通指数を保持する。
使われ方：BS 著者版 Example 7.9 の包絡の有界性。 -/
theorem boundedTorsion_quotient_of_pure_regular_reduction
    (l : E →+* H) (d : E) (hd : IsSMulRegular E d)
    (X : DerivedCategory.Minus (ModuleCat.{u} E))
    (hge : X.obj.IsGE 0) (hle : X.obj.IsLE 0)
    (hreg : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj) d)
    (e : letI := l.toAlgebra
      (DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj ≃ₗ[E] H)
    (p : ℕ)
    (hb : ∃ N : ℕ, ∀ (n : ℕ)
      (x : (DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj),
      (p : E ⧸ Ideal.span {d}) ^ n • x = 0 →
        (p : E ⧸ Ideal.span {d}) ^ N • x = 0) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : H ⧸ (Ideal.span {d}).map l),
      (p : H ⧸ (Ideal.span {d}).map l) ^ n * x = 0 →
        (p : H ⧸ (Ideal.span {d}).map l) ^ N * x = 0 := by
  let := l.toAlgebra
  let I := Ideal.span {d}
  let Q := E ⧸ I
  let V := H ⧸ I.map l
  let := adicQuotientAlgebra I H
  let eH := (pureRegularQuotientH0Iso d hd X hge hle hreg).toLinearEquiv.trans
    (((quotientModuleFunctor I).mapIso e.toModuleIso).toLinearEquiv.trans
      (adicReductionEquivAlgebraQuotient I H))
  obtain ⟨N, hN⟩ := hb
  refine ⟨N, fun n x hx => ?_⟩
  have hpmap (m : ℕ) : (algebraMap Q V) ((p : Q) ^ m) = (p : V) ^ m :=
    (map_pow (algebraMap Q V) (p : Q) m).trans
      (congrArg (fun t : V => t ^ m) (map_natCast (algebraMap Q V) p))
  have hx' : (p : Q) ^ n • x = 0 := by
    change (algebraMap Q V) ((p : Q) ^ n) * x = 0
    exact (congrArg (fun t : V => t * x) (hpmap n)).trans hx
  have hy : (p : Q) ^ N • x = 0 := by
    apply eH.symm.injective
    rw [map_smul, map_zero]
    apply hN n
    simpa only [← eH.symm.map_smul, map_zero] using congrArg eH.symm hx'
  change (algebraMap Q V) ((p : Q) ^ N) * x = 0 at hy
  exact (congrArg (fun t : V => t * x) (hpmap N)).symm.trans hy

end SerrePositivity.DerivedCompletion
