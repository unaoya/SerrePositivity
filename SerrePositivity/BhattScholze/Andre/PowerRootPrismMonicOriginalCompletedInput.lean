module

public import SerrePositivity.BhattScholze.Andre.PowerRootMonicCompletedInput
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletedEquationInput

/-!
# André A1-a：原典の順序の完備入力環からの試験射

## 概要

S=(A/d)⟨Y^(1/p^∞)⟩/(f) から有界試験 prism の商への入力射に対し、
元の H から試験 prism への基底と全入力根を保つ δ 射が一意に存在する。
BS Rem 7.15（著者版 p.62）の完備入力環との接続。

## 方針

モニック商と p 完備化の交換同型で入力射を移し、既存の実完備化の普遍性を適用する。
原典とは異なる全冪商の正則性・通常の完備化と商の普遍性による経路。

## 規約

入力を完備化してからモニック関係で割る。係数環の p 正則性は要求しない。
H 自体の prism 性と絶対 envelope 全体の同定は別工程。

## 使われ方

原典の順序の完備入力射を絶対 envelope の比較に渡す。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "jS" => algebraMap S₀ CS
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})

/-- 概要：原典の順序の完備入力環からの射を保つ H の δ 射は一意に存在。
方針：全入力元を保つ商と完備化の交換同型で既存の普遍性に帰着する。
規約：モニック性を使い、追加の p 正則性・正次数は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の S からの試験データによる比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_original_completed_input
    (hf : f.Monic)
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q) (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (powerRootPolynomialVariable A p hp n)))) =
              η (lS (powerRootPolynomialVariable R p hp n)) := by
  let := pdCompletionCommRing L p (jL dP)
  let e := powerRootMonicCompletedInputEquiv p hp fR (hf.map (Ideal.Quotient.mk W.ideal))
  have he (x : PR) : e.symm (jS (qR x)) = lS x := by
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (powerRootMonicCompletedInputEquiv_coeff p hp fR
        (hf.map (Ideal.Quotient.mk W.ideal)) x).symm
  let ηC := η.comp e.symm.toRingHom
  have hc : (ηC.comp jS).comp (powerRootEquationQuotientCoeff p hp fR) =
      k.quotientMap := by
    apply RingHom.ext
    intro x
    change η (e.symm (jS (qR (algebraMap R PR x)))) = k.quotientMap x
    rw [he]
    exact RingHom.congr_fun hη x
  obtain ⟨F, hF, hu⟩ :=
    existsUnique_powerRootPrismMonicCompletionHom_of_completed_equation_input
      W hW f Q hB k ηC hc
  refine ⟨F, ⟨hF.1, hF.2.1, ?_⟩, ?_⟩
  · intro n
    exact (hF.2.2 n).trans (congrArg η (he (powerRootPolynomialVariable R p hp n)))
  · intro K hK
    apply hu K
    refine ⟨hK.1, hK.2.1, ?_⟩
    intro n
    change Ideal.Quotient.mk Q.ideal
      (K (uL (jL (powerRootPolynomialVariable A p hp n)))) =
        η (e.symm (jS (qR (powerRootPolynomialVariable R p hp n))))
    rw [he]
    exact hK.2.2 n

end SerrePositivity.BhattScholze.Andre
