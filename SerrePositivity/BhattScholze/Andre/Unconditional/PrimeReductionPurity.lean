module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawPDCompletelyFlat
public import SerrePositivity.BhattScholze.PerfectDeltaModP
public import SerrePositivity.BhattScholze.PDCompletionInterface
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-!
# 元の源の先行 p 還元と実完備化の p 正則性

## 概要
BS Rem 7.15（著者版 p.62）の元の実逐次完備化を先に p で還元し、その純性を示す。

## 方針
A/(p) の被約性による d ねじれの上界と、実二生成剰余の純性・平坦性を使う。

## 規約
hpR や d mod p の正則性は要求しない。raw 環の p 正則性は結論しない。

## 使われ方
元の実完備化 H の p 正則性へ、標準 A 作用を保持して移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- 概要：被約環の任意主元の冪ねじれは、その主元で零になる。
方針：積の冪が零になることから被約性を使う。
規約：零環と冪零指数零も含める。
使われ方：BS Rem 7.15（著者版 p.62）の A/(p) での有界ねじれ入力。 -/
theorem unconditionalReduced_power_torsion_bound
    {K : Type u} [CommRing K] [IsReduced K] (d : K) (n : ℕ) (x : K)
    (h : d ^ n * x = 0) : d * x = 0 := by
  apply IsNilpotent.eq_zero
  refine ⟨n + 1, ?_⟩
  calc
    (d * x) ^ (n + 1) = (d ^ n * x) * (d * x ^ n) := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    _ = 0 := by rw [h, zero_mul]

section DoubleReduction
variable {A : Type u} [CommRing A] (a b : A)
local notation "QA" => A ⧸ Ideal.span (Set.singleton a)
local notation "qA" => Ideal.Quotient.mk (Ideal.span (Set.singleton a))
local notation "QB" => QA ⧸ Ideal.span (Set.singleton (qA b))
local notation "qB" => Ideal.Quotient.mk (Ideal.span (Set.singleton (qA b)))
local notation "Q" => A ⧸ Ideal.span (Set.insert a (Set.singleton b))
local notation "q" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton b)))
local notation "e" => principalDoubleQuotEquiv a b

/-- 概要：標準二段主商の係数拡大を同じ二生成商への拡大・係数制限へ比較する。
方針：全代表元を保つ二重商同型と標準係数拡大合成を使う。
規約：a,b の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の先行 p 還元の実剰余比較。 -/
def unconditionalDoubleReductionCochainIso :
    (ModuleCat.extendScalars qA).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars qB).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (e).toRingHom).mapHomologicalComplex (.up ℤ) := by
  have h : (qB).comp qA = (e).symm.toRingHom.comp q := by
    apply RingHom.ext
    intro x
    apply (e).injective
    change (e) ((qB) ((qA) x)) = (e) ((e).symm ((q) x))
    rw [RingEquiv.apply_symm_apply]
    exact principalDoubleQuotEquiv_mk a b x
  let eS : ModuleCat.extendScalars qA ⋙ ModuleCat.extendScalars qB ≅
      ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars (e).toRingHom :=
    (ModuleCat.extendScalarsComp qA qB).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars h) ≪≫
      ModuleCat.extendScalarsComp q (e).symm.toRingHom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars q)
        (restrictScalarsIsoExtendInverse e).symm
  exact Functor.mapHomologicalComplexCompIso eS (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars (e).toRingHom))
      (.up ℤ)).symm

/-- 概要：同じ二段主商比較を実導来対象に適用する。
方針：選択射影モデルと元の係数拡大モデルの比較を合成する。
規約：元の導来対象を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の先行 p 還元の純性判定。 -/
def unconditionalDoubleReductionDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange qB).obj ((boundedAboveDerivedBaseChange qA).obj X) ≅
      (boundedAboveDerivedRestrictScalars (e).toRingHom).obj
        ((boundedAboveDerivedBaseChange q).obj X) :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedBaseChangeModelIso qB ((boundedAboveDerivedBaseChange qA).obj X)
        (boundedAboveDerivedBaseChangeModel qA X) ≪≫
      DerivedCategory.Q.mapIso ((unconditionalDoubleReductionCochainIso a b).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      ((derivedRestrictScalarsFactors (e).toRingHom).app
        (baseChange q (boundedAboveDerivedChosenModel X).complex)).symm ≪≫
      (derivedRestrictScalars (e).toRingHom).mapIso
        (boundedAboveDerivedBaseChangeModelIso q X (boundedAboveDerivedChosenModel X)).symm)

/-- 概要：実二段主商のホモロジーを同じ二生成商ホモロジーの係数制限へ比較する。
方針：実導来比較と正確な係数制限を合成する。
規約：全整数次数に適用する。
使われ方：BS Rem 7.15（著者版 p.62）の消滅と平坦性の移送。 -/
def unconditionalDoubleReductionHomologyIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat QB) i).obj
        ((boundedAboveDerivedBaseChange qB).obj ((boundedAboveDerivedBaseChange qA).obj X)).obj ≅
      (ModuleCat.restrictScalars (e).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
          ((boundedAboveDerivedBaseChange q).obj X).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat QB) i).mapIso
      (DerivedCategory.Minus.ι.mapIso (unconditionalDoubleReductionDerivedIso a b X)) ≪≫
    (derivedRestrictScalarsHomologyIso (e).toRingHom i).app
      ((boundedAboveDerivedBaseChange q).obj X).obj

/-- 概要：二生成商の H⁰ 平坦性は実二段主商へ移る。
方針：商環同型の係数制限とホモロジー比較を使う。
規約：正則性を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の有界ねじれ純性判定への平坦性入力。 -/
theorem unconditionalDoubleReductionH0_flat
    (X : DerivedCategory.Minus (ModuleCat.{u} A))
    (h : Module.Flat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)) :
    Module.Flat QB ((DerivedCategory.homologyFunctor (ModuleCat QB) 0).obj
      ((boundedAboveDerivedBaseChange qB).obj ((boundedAboveDerivedBaseChange qA).obj X)).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
    ((boundedAboveDerivedBaseChange q).obj X).obj
  let := (e).toRingHom.toAlgebra
  let : Module QB M := Module.compHom M (e).toRingHom
  let : IsScalarTower QB Q M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : QB ≃ₐ[QB] Q := AlgEquiv.ofBijective (Algebra.ofId QB Q) (e).bijective
  have : Module.Flat QB Q := Module.Flat.of_linearEquiv eA.symm.toLinearEquiv
  have : Module.Flat Q M := h
  have : Module.Flat QB M := Module.Flat.trans QB Q M
  exact Module.Flat.of_linearEquiv (R := QB) (M := M)
    (unconditionalDoubleReductionHomologyIso a b X 0).toLinearEquiv
end DoubleReduction

/-- 概要：別の主元に関して導来完備な対象の正則主商も、商環上で導来完備。
方針：正則主商を実 Koszul 錐で計算し、係数制限で完備性を反映する。
規約：商にする元だけの正則性を要求する。
使われ方：BS Rem 7.15（著者版 p.62）の先行 p 還元の d 完備性。 -/
theorem unconditionalRegularQuotient_isComplete
    {A : Type u} [CommRing A] (a b : A) (ha : IsSMulRegular A a)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (hc : IsComplete A b X.obj) :
    IsComplete (A ⧸ Ideal.span (Set.singleton a))
      (Ideal.Quotient.mk (Ideal.span (Set.singleton a)) b)
      ((boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span (Set.singleton a)))).obj X).obj := by
  let q := Ideal.Quotient.mk (Ideal.span (Set.singleton a))
  let T := A ⧸ Ideal.span (Set.singleton a)
  let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
  let F := derivedRestrictScalars q
  let K := DerivedCategory.Q.objPreimage X.obj
  let eK := DerivedCategory.Q.objObjPreimageIso X.obj
  have hK : IsComplete A b (DerivedCategory.Q.obj K) := isComplete_of_iso A b eK.symm hc
  have hCone := isComplete_Q_mappingCone A b (smulId a K) hK hK
  let e := restrictedDerivedQuotientKoszulIso a ha X ≪≫
    (derivedScalarConeFunctor A a).mapIso eK.symm ≪≫ (derivedScalarConeComparison A a).app K
  have hR : IsComplete A b (F.obj Y) := isComplete_of_iso A b e.symm hCone
  have hunitR : IsIso ((derivedComplexCompletionUnit A b).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A b (F.obj Y) hR
  let eC := derivedRestrictionCompletionIso q b
  have hc' : IsIso (F.map ((derivedComplexCompletionUnit T (q b)).app Y) ≫ eC.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q b)).app Y)) :=
    IsIso.of_isIso_comp_right _ (eC.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q b)).app Y) := isIso_of_reflects_iso _ F
  exact (isComplete_iff_derivedComplexCompletionUnit_isIso T (q b) Y).mpr hS

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "d" => W.generator
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
local notation "K" => A ⧸ Ideal.span {(p : A)}
local notation "qP" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "dd" => qP d
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qP) XC
local notation "Q" => A ⧸ Ideal.span {(p : A), d}
local notation "qPD" => Ideal.Quotient.mk (Ideal.span {(p : A), d})

/-- 概要：元の実逐次完備化の先行 p 還元は次数零に集中する。
方針：A/(p) の d 冪ねじれ上界、実二生成剰余の純性・平坦性、商上の d 完備性を使う。
規約：d mod p の正則性も hpR も仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の実完備化の p 正則性。 -/
theorem powerRootPrismMonicSourcePrimeReduction_pure_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (Y).obj.IsGE 0 ∧ (Y).obj.IsLE 0 := by
  apply derived_pure_of_complete_flat_reduction dd Y
  · intro i hi
    let e := unconditionalDoubleReductionHomologyIso (p : A) d XC i
    exact ((ModuleCat.restrictScalars (principalDoubleQuotEquiv (p : A) d).toRingHom).map_isZero
      (powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional
        W hW f hf i hi)).of_iso e
  · exact unconditionalDoubleReductionH0_flat (p : A) d XC
      (powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient W hW f
        (InitialCoefficient.sourceResidueH0_faithfullyFlat W hW f hf hdeg)).1
  · let := hW.perfectRing_mod_p
    let : IsReduced K :=
      (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr (by
        intro x hx
        exact (PerfectRing.bijective_frobenius (R := K) (p := p)).1
          (by simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using hx))
    exact ⟨1, fun n x hx => by
      simpa only [pow_one] using unconditionalReduced_power_torsion_bound dd n x hx⟩
  · exact unconditionalRegularQuotient_isComplete (p : A) d hW.p_mul_injective XC
      (powerRootPrismMonicSourceIteratedPDCompletion_isComplete_d_of_unconditional W hW f)

/-- 概要：元の実逐次完備化の H⁰ で p は単射に作用する。
方針：先行 p 商の純性と元の p 導来完備性を正則商純性判定に渡す。
規約：元の A 上の実対象で述べ、raw の p 正則性は使わない。
使われ方：BS Rem 7.15（著者版 p.62）の元の H の p 正則性への移送。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_prime_injective_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XC).obj => (p : A) • x) := by
  apply (derived_pure_of_complete_regular_quotient_pure (p : A) hW.p_mul_injective XC
    (powerRootPrismMonicSourceIteratedPDCompletion_isComplete_p_of_unconditional W hW f) ?_).2.2
  intro i hi
  obtain ⟨hGE, hLE⟩ := powerRootPrismMonicSourcePrimeReduction_pure_of_unconditional W hW f hf hdeg
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i hlt
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i hgt

local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P d
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "c" => algebraMap A Raw
local notation "H" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw H)

/-- 概要：元の raw PD 実完備化 H には p ねじれがない。
方針：元の実源 H⁰ の p 単射性を標準 A 線形比較で移す。
規約：hpR・raw p 正則性を仮定せず、元の H の環構造を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の p 正則性の無条件版。 -/
theorem powerRootPrismMonic_pdCompletion_prime_regular_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular H (p : H) := by
  let := pdCompletionCommRing Raw p (c d)
  let := pdCompletionAlgebra Raw p (c d)
  let e := (powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f).toLinearEquiv
  have hsrc := powerRootPrismMonicSourceIteratedPDCompletion_prime_injective_of_unconditional
    W hW f hf hdeg
  have hM : Function.Injective (fun x : ModuleCat.carrier M => (p : A) • x) := by
    intro x y hxy
    apply e.symm.injective
    apply hsrc
    simpa only [← e.symm.map_smul] using congrArg e.symm hxy
  change Function.Injective (fun x : H => (p : H) * x)
  intro x y hxy
  apply hM
  change (p : Raw) • (x : H) = (p : Raw) • (y : H)
  simpa only [Algebra.smul_def, map_natCast] using hxy

/-- 概要：次数零モニック入力では元の実完備化 H は零環。
方針：f=1 から標準分母像の乗法逆元を作り、同じ分母での導来完備性を使う。
規約：元の raw 包と元の実 H⁰ のままで述べる。
使われ方：BS Rem 7.15（著者版 p.62）の正則性を余分な正次数仮定なしに述べる。 -/
theorem powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero
    (hf : f.Monic) (hz : f.natDegree = 0) :
    let := pdCompletionCommRing Raw p (c d)
    Subsingleton H := by
  let := pdCompletionCommRing Raw p (c d)
  have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hz
  let v := deltaAdjoinDivisionVariable E dP a (PUnit.unit : PUnit.{u + 1})
  have ha1 : a (PUnit.unit : PUnit.{u + 1}) = (1 : P) := by
    simp only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput, hf1, map_one]
  have hv : c d * v = 1 := by
    have h := deltaAdjoinDivision_relation E dP a (PUnit.unit : PUnit.{u + 1})
    rw [ha1, map_one] at h
    exact h
  let j := pdCompletionUnit Raw p (c d)
  have hvH : j (c d) * j v = 1 := by
    simpa only [map_mul, map_one] using congrArg j hv
  have hs : Function.Surjective (fun x : H => j (c d) • x) := by
    intro x
    refine ⟨j v * x, ?_⟩
    change j (c d) * (j v * x) = x
    rw [← mul_assoc, hvH, one_mul]
  have hzero := isZero_of_complete_of_smul_surjective (j (c d)) (ModuleCat.of H H)
    (pdCompletionH0_self_complete_d Raw p (c d)) hs
  change Subsingleton (ModuleCat.of H H)
  exact ModuleCat.isZero_iff_subsingleton.mp hzero

/-- 概要：元の実完備化 H は、任意のモニック入力について p 正則。
方針：正次数では先行 p 還元の純性、次数零では同じ H の零環性を使う。
規約：旧定理から hpR だけを除き、正次数仮定を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の実 H の p 正則性の置換先。 -/
theorem powerRootPrismMonic_pdCompletion_prime_regular_of_unconditional
    (hf : f.Monic) :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular H (p : H) := by
  by_cases hz : f.natDegree = 0
  · let := pdCompletionCommRing Raw p (c d)
    let : Subsingleton H :=
      powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
    change Function.Injective (fun x : H => (p : H) * x)
    intro x y _
    exact Subsingleton.elim x y
  · exact powerRootPrismMonic_pdCompletion_prime_regular_of_positive_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：元の H の標準分母像は、任意のモニック入力について正則。
方針：正次数の場合の実源の純性と、次数零の場合の H の零環性を合流する。
規約：旧定理の hf を保持し、hpR と余分な正次数仮定を置かない。
使われ方：BS Rem 7.15（著者版 p.62）の元の H の prism 構造への入力。 -/
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular_of_monic_unconditional
    (hf : f.Monic) :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular H (pdCompletionUnit Raw p (c d) (c d)) := by
  by_cases hz : f.natDegree = 0
  · let := pdCompletionCommRing Raw p (c d)
    let : Subsingleton H :=
      powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
    change Function.Injective (fun x : H => pdCompletionUnit Raw p (c d) (c d) * x)
    intro x y _
    exact Subsingleton.elim x y
  · exact powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

end SerrePositivity.BhattScholze.Andre
