module

public import SerrePositivity.HomologicalAlgebra.DerivedScalarExtensionComposition
public import SerrePositivity.HomologicalAlgebra.KoszulRegularBaseChange
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.CompletedFlatBoundedTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-!
# 正則関係の商に帰着する二座標完備底変換

## 概要
生成元剰余で正則関係の商を経由する導来底変換を、その商の完全平坦な底変換へ移す。
商の p 冪ねじれが有界なら離散性と生成元の正則性が従う。

## 方針
可換四角形と Koszul 分解で剰余を比較し、主元完備化の既存の純性判定を使う。

## 規約
通常の上に有界な導来圏を用いる。すべての係数作用は環射として明示する。

## 使われ方
BS 著者版 Example 7.9 の一般の正則列に沿う包絡候補。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits DerivedCompletion

attribute [local instance] HasDerivedCategory.standard

variable {U E A : Type u} [CommRing U] [CommRing E] [CommRing A]
/-- 概要：係数射に沿う主元剰余の標準射。
方針：生成元を送ったイデアルへの通常の商射を使う。
規約：始域と終域のイデアルを明示する。
使われ方：BS 著者版 Example 7.9 の剰余比較。 -/
abbrev regularRelationCoefficientHom (c : U →+* A) (a : U) :=
  (Ideal.quotientMap («I» := (Ideal.span {a})) (Ideal.map c (Ideal.span {a})) c (Ideal.le_comap_map
      («I» := (Ideal.span {a})) (f := c)))

/-- 概要：関係列の商に誘導される標準係数射。
方針：主元剰余の標準射を関係の生成イデアルで割る。
規約：関係の正則性によらない通常の環射。
使われ方：BS 著者版 Example 7.9 の有界な関係商。 -/
abbrev regularRelationQuotientHom (c : U →+* A) (a : U)
    {r : ℕ} (z : Fin r → U ⧸ Ideal.span {a}) :=
  (Ideal.quotientMap («I» := (Ideal.span (Set.range z))) (Ideal.map (regularRelationCoefficientHom c
      a) (Ideal.span (Set.range z))) (regularRelationCoefficientHom c a) (Ideal.le_comap_map («I» :=
      (Ideal.span (Set.range z))) (f := (regularRelationCoefficientHom c a))))

/-- 概要：指定した係数加群の導来底変換。
方針：制限した係数環を零次に置き、指定の環射で導来係数拡大する。
規約：通常の上に有界な導来圏の対象。
使われ方：BS 著者版 Example 7.9 の二座標完備化への入力。 -/
abbrev regularRelationBaseChangeObject (α : U →+* E) (c : U →+* A) :=
  (Functor.obj (boundedAboveDerivedBaseChange α) (Functor.obj boundedAboveDerivedSingleFunctor
      (baseChangeScalarModule c)))

variable (α : U →+* E) (c : U →+* A) (a : U) (d : E)

variable {r : ℕ} (z : Fin r → (U ⧸ (Ideal.span {a})))

set_option maxHeartbeats 1000000 in
/-- 概要：生成元剰余の導来底変換は、初期関係を除いた通常商の残る係数拡大。
方針：可換四角形を二段の係数拡大に移し、二つの Tor 消滅で通常の商を取り出す。
規約：正則性は源の主元、係数環でのその像、二つの関係列に仮定する。
使われ方：正則列の商に沿う二座標完備化の計算。 -/
def regularRelationBaseChangeReductionIso
    (b : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range z))) →+* (E ⧸ Ideal.span {d}))
    (hsq : ((Ideal.Quotient.mk (Ideal.span {d}))).comp α = ((b).comp (Ideal.Quotient.mk (Ideal.span
        (Set.range z)))).comp (Ideal.Quotient.mk (Ideal.span {a})))
    (ha : IsSMulRegular U a) (hc : IsSMulRegular A (c a))
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution ((regularRelationCoefficientHom c a) ∘ z)) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj
        (regularRelationBaseChangeObject α c) ≅
      (boundedAboveDerivedBaseChange b).obj
        (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule (regularRelationQuotientHom c
            a z))) := by
  have hcM : IsSMulRegular (baseChangeScalarModule c) a := by
    change Function.Injective (fun x : A => c a * x)
    change Function.Injective (fun x : A => c a * x) at hc
    exact hc
  let e₀ := derivedQuotientScalarModuleIso c (Ideal.span {a})
    (scalarExtensionTorVanishing_principal_of_regular a ha (baseChangeScalarModule c) hcM)
  exact boundedAboveDerivedBaseChangeSquareIso α (Ideal.Quotient.mk (Ideal.span {d}))
      (Ideal.Quotient.mk (Ideal.span {a})) (b.comp (Ideal.Quotient.mk (Ideal.span (Set.range z))))
      hsq (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule c)) ≪≫
    (boundedAboveDerivedBaseChange (b.comp (Ideal.Quotient.mk (Ideal.span (Set.range z))))).mapIso
        e₀ ≪≫
    boundedAboveDerivedBaseChangeCompositionIso (Ideal.Quotient.mk (Ideal.span (Set.range z))) b
      (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule (regularRelationCoefficientHom c
          a))) ≪≫
    (boundedAboveDerivedBaseChange b).mapIso (derivedRegularQuotientScalarIso
        (regularRelationCoefficientHom c a) z hz hf)

private def completionGeneratorReductionIso
    (hd : IsSMulRegular E d) (W : DerivedCategory.Minus (ModuleCat.{u} E)) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj W ≅
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj
        ((boundedAboveDerivedCompletionFunctor E d).obj W) := by
  let F (t : E) := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {t}))).obj W ≅
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {t}))).obj
      ((boundedAboveDerivedCompletionFunctor E d).obj W)
  exact Eq.mp (congrArg F (_root_.pow_one d))
    (boundedAboveDerivedCompletionQuotientIso E d hd 1 W)

set_option maxHeartbeats 1000000 in
/-- 概要：p 完備化の後の d 剰余は、正則関係の商の完全平坦な p 完備底変換。
方針：d 完備化は d 剰余を保ち、p 完備化と正則な d 剰余は交換する。
規約：係数の p 冪ねじれの上界を保持する。
使われ方：BS 著者版 Example 7.9 の完備源の離散性。 -/
theorem completedRegularRelationReduction_pure_bounded
    (b : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range z))) →+* (E ⧸ Ideal.span {d}))
    (hsq : ((Ideal.Quotient.mk (Ideal.span {d}))).comp α = ((b).comp (Ideal.Quotient.mk (Ideal.span
        (Set.range z)))).comp (Ideal.Quotient.mk (Ideal.span {a})))
    (ha : IsSMulRegular U a) (hc : IsSMulRegular A (c a))
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution ((regularRelationCoefficientHom c a) ∘ z))
    (p : ℕ) (hd : IsSMulRegular E d)
    (hflat : IsCompletelyFlat (Ideal.span {(p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range
        z))))}) (baseChangeScalarModule b))
    (hR : ∃ N : ℕ, ∀ (n : ℕ) (x : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map
        (regularRelationCoefficientHom c a) (Ideal.span (Set.range z)))),
      (p : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map (regularRelationCoefficientHom c a)
          (Ideal.span (Set.range z)))) ^ n * x = 0 → (p : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸
          Ideal.map (regularRelationCoefficientHom c a) (Ideal.span (Set.range z)))) ^ N * x = 0) :
    let Z := (boundedAboveDerivedCompletionFunctor E d).obj
      ((boundedAboveDerivedCompletionFunctor E (p : E)).obj (regularRelationBaseChangeObject α c))
    let W := ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj Z).obj
    W.IsGE 0 ∧ W.IsLE 0 ∧
      ∃ N : ℕ, ∀ (n : ℕ)
        (x : (DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).obj W),
        (p : (E ⧸ Ideal.span {d})) ^ n • x = 0 → (p : (E ⧸ Ideal.span {d})) ^ N • x = 0 := by
  let Z := (boundedAboveDerivedCompletionFunctor E d).obj
    ((boundedAboveDerivedCompletionFunctor E (p : E)).obj (regularRelationBaseChangeObject α c))
  let W := ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj Z).obj
  let Fp := derivedComplexCompletionFunctor (E ⧸ Ideal.span {d}) (p : (E ⧸ Ideal.span {d}))
  let V := ((boundedAboveDerivedBaseChange b).obj
    (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule (regularRelationQuotientHom c a
        z)))).obj
  let e : W ≅ Fp.obj V :=
    (DerivedCategory.Minus.ι.mapIso (completionGeneratorReductionIso d hd
      ((boundedAboveDerivedCompletionFunctor E (p : E)).obj (regularRelationBaseChangeObject α
          c)))).symm ≪≫
    (completionQuotientBaseChangeIso E (p : E) d hd (regularRelationBaseChangeObject α c)).symm ≪≫
    Fp.mapIso (DerivedCategory.Minus.ι.mapIso
      (regularRelationBaseChangeReductionIso α c a d z b hsq ha hc hz hf))
  obtain ⟨N, hN⟩ := hR
  have hM : ∀ (n : ℕ) (x : baseChangeScalarModule (regularRelationQuotientHom c a z)),
      (p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range z)))) ^ n • x = 0 → (p : ((U ⧸
          (Ideal.span {a})) ⧸ (Ideal.span (Set.range z)))) ^ N • x = 0 := by
    intro n x hx
    have hxR : (p : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map (regularRelationCoefficientHom c
        a) (Ideal.span (Set.range z)))) ^ n * (show ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map
        (regularRelationCoefficientHom c a) (Ideal.span (Set.range z))) from x) = 0 := by
      change (regularRelationQuotientHom c a z) ((p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span
          (Set.range z)))) ^ n) * (show ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map
          (regularRelationCoefficientHom c a) (Ideal.span (Set.range z))) from x) = 0 at hx
      simpa only [map_pow, map_natCast] using hx
    change (regularRelationQuotientHom c a z) ((p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range
        z)))) ^ N) * (show ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map
        (regularRelationCoefficientHom c a) (Ideal.span (Set.range z))) from x) = 0
    rw [map_pow, map_natCast]
    exact hN n _ hxR
  have hpure : (Fp.obj V).IsGE 0 ∧ (Fp.obj V).IsLE 0 ∧
      ∀ (n : ℕ) (x : (DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).obj
          (Fp.obj V)),
        (p : (E ⧸ Ideal.span {d})) ^ n • x = 0 → (p : (E ⧸ Ideal.span {d})) ^ N • x = 0 := by
    let G (t : (E ⧸ Ideal.span {d})) : Prop :=
      let Wt := (derivedComplexCompletionFunctor (E ⧸ Ideal.span {d}) t).obj V
      Wt.IsGE 0 ∧ Wt.IsLE 0 ∧
        ∀ (n : ℕ) (x : (DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).obj Wt),
          t ^ n • x = 0 → t ^ N • x = 0
    have h : G (b (p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range z))))) :=
        completedBaseChange_bounded_torsion_pure b (p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span
        (Set.range z)))) hflat
      (baseChangeScalarModule (regularRelationQuotientHom c a z)) N hM
    have hbp : b (p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range z)))) = (p : (E ⧸ Ideal.span
        {d})) := map_natCast b p
    exact Eq.mp (congrArg G hbp) h
  have hGE : W.IsGE 0 := by
    let := hpure.1
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have hLE : W.IsLE 0 := by
    let := hpure.2.1
    exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  refine ⟨hGE, hLE, N, ?_⟩
  intro n x hx
  let eH := ((DerivedCategory.homologyFunctor (ModuleCat (E ⧸ Ideal.span {d})) 0).mapIso
      e).toLinearEquiv
  apply eH.injective
  rw [map_smul, map_zero]
  apply hpure.2.2 n
  simpa only [← eH.map_smul, map_zero] using congrArg eH hx

set_option maxHeartbeats 1000000 in
/-- 概要：正則関係の商を経由する完備底変換は離散で、指定の生成元は H⁰ に正則。
方針：剰余の離散性と導来 d 完備性に既存の正則商による純性判定を適用する。
規約：有界な p 冪ねじれは関係の商にだけ仮定する。
使われ方：BS 著者版 Example 7.9 の通常の環候補に prism 構造を付ける。 -/
theorem completedRegularRelationBaseChange_pure_regular
    (b : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range z))) →+* (E ⧸ Ideal.span {d}))
    (hsq : ((Ideal.Quotient.mk (Ideal.span {d}))).comp α = ((b).comp (Ideal.Quotient.mk (Ideal.span
        (Set.range z)))).comp (Ideal.Quotient.mk (Ideal.span {a})))
    (ha : IsSMulRegular U a) (hc : IsSMulRegular A (c a))
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution ((regularRelationCoefficientHom c a) ∘ z))
    (p : ℕ) (hd : IsSMulRegular E d)
    (hflat : IsCompletelyFlat (Ideal.span {(p : ((U ⧸ (Ideal.span {a})) ⧸ (Ideal.span (Set.range
        z))))}) (baseChangeScalarModule b))
    (hR : ∃ N : ℕ, ∀ (n : ℕ) (x : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map
        (regularRelationCoefficientHom c a) (Ideal.span (Set.range z)))),
      (p : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸ Ideal.map (regularRelationCoefficientHom c a)
          (Ideal.span (Set.range z)))) ^ n * x = 0 → (p : ((A ⧸ Ideal.map c (Ideal.span {a})) ⧸
          Ideal.map (regularRelationCoefficientHom c a) (Ideal.span (Set.range z)))) ^ N * x = 0) :
    let Z := (boundedAboveDerivedCompletionFunctor E d).obj
      ((boundedAboveDerivedCompletionFunctor E (p : E)).obj (regularRelationBaseChangeObject α c))
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat E) 0).obj Z.obj =>
        d • x) := by
  let Z := (boundedAboveDerivedCompletionFunctor E d).obj
    ((boundedAboveDerivedCompletionFunctor E (p : E)).obj (regularRelationBaseChangeObject α c))
  have hred := completedRegularRelationReduction_pure_bounded α c a d z b hsq ha hc hz hf
    p hd hflat hR
  have hcZ : IsComplete E d Z.obj := derivedComplexCompletionFunctor_isComplete E d _
  apply derived_pure_of_complete_regular_quotient_pure d hd Z hcZ
  intro i hi
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact (DerivedCategory.isGE_iff _ _).mp hred.1 i hlt
  · exact (DerivedCategory.isLE_iff _ _).mp hred.2.1 i hgt

end SerrePositivity
