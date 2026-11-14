module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmall
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawCoefficientPD
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmall
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 有限枠上の Witt 係数変更

## 概要
Witt の大きい枠を経由した係数変更は、小さい模型に制限すると第 0 Witt 成分による係数変更。

## 方針
有限枠を分冪包として読み、未完備模型からの二つの分冪射を各頂点の変数で照合する。

## 規約
剰余係数の p 正則性と p 完備性を仮定する。

## 使われ方
BS 著者版 Theorem 6.4 の係数変更の検査を有限枠へ移す。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "Jw" => wittPdIdeal p C
local notation "Ic" => Ideal.span {(p : C)}

local instance : Algebra W C := (wZero p C).toAlgebra

variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))
variable (Q : Poly (A ⧸ P.ideal))

local notation "γW" => wittPdStructure p C hpC hlocal
local notation "γC" => residuePdStructure p hpC hlocal
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "hp'" => WittToSmall.hp P
local notation "hkW" => wittComplete P hpC hk
local notation "hpRegW" => witt_mul_prime_injective p C hpC
local notation "hw" => smallResidue_ker P Q
local notation "sw" => smallFrame P Q
local notation "hc" => PDPolynomialFunctor.base_ker (J := Ic) Q
local notation "sc" => PDPolynomialFunctor.frame (J := Ic) Q
local notation "hb" => bigResidue_ker_witt P Q
local notation "sb" => largeFrame P Q
local notation "smB" => smallFrameOnBigResidue P hpC Q
local notation "Dw" => PDCechNerve.term p γW hpW hw sw
local notation "Dc" => PDCechNerve.term p γC hp' hc sc
local notation "Db" => PDCechNerve.term p γW hpW hb sb

private def frameInclusion (n : ℕ) : (Dw n).carrier →ₐ[W] (Db n).carrier :=
  (PDCechNerve.mapAt p γW hpW hb smB sb (frameLift P hpC hlocal Q)
    (frameLift_spec P hpC hlocal Q) n).comp
    (PDCechNerve.renameAt p γW hpW hw hb sw smB (smallResidueEquiv P hpC Q).toAlgHom
      id (fun _ => rfl) n)

private theorem frameInclusion_dp (n : ℕ) :
    (Dw n).dividedPowers.IsDPMorphism (Db n).dividedPowers
      (frameInclusion P hpC hlocal Q n).toRingHom :=
  (PDCechNerve.mapAt_isDPMorphism p γW hpW hb smB sb (frameLift P hpC hlocal Q)
    (frameLift_spec P hpC hlocal Q) n).comp _
    (PDCechNerve.renameAt_isDPMorphism p γW hpW hw hb sw smB
      (smallResidueEquiv P hpC Q).toAlgHom id (fun _ => rfl) n)

private theorem frameInclusion_X (n : ℕ) (j : ULift.{u} (Fin Q.n)) (i : Fin (n + 1)) :
    frameInclusion P hpC hlocal Q n (PDCechNerve.variableImage p γW hpW hw sw n (j, i)) =
      PDCechNerve.variableImage p γW hpW hb sb n (smallIndex P Q j, i) := by
  unfold frameInclusion
  simp only [AlgHom.comp_apply, PDCechNerve.renameAt_variableImage, id_eq,
    PDCechNerve.mapAt_variableImage, frameLift, PDCechNerve.mapCopies_variableImage]

private def rawLeft (n : ℕ) : pdRaw W Q.n n →+* (Dc n).carrier := by
  let := WittToSmall.smallWittAlgebra P hpC hlocal Q n
  exact (WittToSmall.mapAt P hpC hlocal Q n).toRingHom.comp
    ((frameInclusion P hpC hlocal Q n).toRingHom.comp
      (PDSmallModelComparison.rawToFrame p W γW hpW hkW hpRegW Q.n hw n).toRingHom)

private def rawRight (n : ℕ) : pdRaw W Q.n n →+* (Dc n).carrier :=
  (PDSmallModelComparison.rawToFrame p C γC hp' hk hpC Q.n hc n).toRingHom.comp
    (pdRawCoefficients W C Q.n n).toRingHom

private theorem raw_square (n : ℕ) :
    rawLeft P hpC hlocal hk Q n = rawRight P hpC hlocal hk Q n := by
  let := WittToSmall.smallWittAlgebra P hpC hlocal Q n
  let f : pdRaw W Q.n n →ₐ[W] (Dc n).carrier :=
    (WittToSmall.mapAt P hpC hlocal Q n).comp
      ((frameInclusion P hpC hlocal Q n).comp
        (PDSmallModelComparison.rawToFrame p W γW hpW hkW hpRegW Q.n hw n))
  let g : pdRaw W Q.n n →ₐ[W] (Dc n).carrier :=
    ⟨rawRight P hpC hlocal hk Q n, fun x => by
      change PDSmallModelComparison.rawToFrame p C γC hp' hk hpC Q.n hc n
        (pdRawCoefficients W C Q.n n (algebraMap W _ x)) =
        algebraMap C (Dc n).carrier (wZero p C x)
      rw [(pdRawCoefficients W C Q.n n).commutes,
        IsScalarTower.algebraMap_apply W C (pdRaw C Q.n n)]
      exact (PDSmallModelComparison.rawToFrame p C γC hp' hk hpC Q.n hc n).commutes _⟩
  have hf := (WittToSmall.mapAt_isDPMorphism P hpC hlocal Q n).comp _
    ((frameInclusion_dp P hpC hlocal Q n).comp _
      (PDSmallModelComparison.rawToFrame_isDPMorphism p W γW hpW hkW hpRegW Q.n hw n))
  have hg := (PDSmallModelComparison.rawToFrame_isDPMorphism p C γC hp' hk hpC Q.n hc n).comp _
    (pdRawCoefficients_isDPMorphism p Q.n n γW γC hkW hk hpRegW hpC
      (wZero_isDPMorphism p C hpC hlocal))
  suffices h : f = g by
    exact congrArg AlgHom.toRingHom h
  apply PDSmallRawEnvelope.hom_ext p Q.n n γW hkW hpRegW (Dc n).dividedPowers
    (g₁ := f) (g₂ := g) hf
    (show (PDSmallRawEnvelope.dividedPowers p Q.n n γW hkW hpRegW).IsDPMorphism
      (Dc n).dividedPowers g.toRingHom from hg)
  apply MvPolynomial.algHom_ext
  rintro ⟨j, i⟩
  change WittToSmall.mapAt P hpC hlocal Q n
    (frameInclusion P hpC hlocal Q n
      (PDSmallModelComparison.rawToFrame p W γW hpW hkW hpRegW Q.n hw n
        (PDSmallRawEnvelope.unit Q.n n (MvPolynomial.X (j, i))))) =
    PDSmallModelComparison.rawToFrame p C γC hp' hk hpC Q.n hc n
      (pdRawCoefficients W C Q.n n (PDSmallRawEnvelope.unit Q.n n (MvPolynomial.X (j, i))))
  rw [PDSmallModelComparison.rawToFrame_unit]
  change WittToSmall.mapAt P hpC hlocal Q n
    (frameInclusion P hpC hlocal Q n (PDCechNerve.variableImage p γW hpW hw sw n (j, i))) = _
  rw [frameInclusion_X P hpC hlocal Q n j i]
  change WittToSmall.mapAt P hpC hlocal Q n
    (PDCechNerve.variableImage p γW hpW (WittToSmall.wittBaseKer P Q)
      (Ideal.Quotient.mk _) n (smallIndex P Q j, i)) = _
  rw [WittToSmall.mapAt_X, smallIndex, WittToSmall.eval_unit]
  rw [PDSmallRawEnvelope.unit_X, pdRawCoefficients_copy W C Q.n ⦋n⦌ j.down i,
    ← PDSmallRawEnvelope.unit_X (k := C) Q.n n (j, i), PDSmallModelComparison.rawToFrame_unit]
  exact MvPolynomial.aeval_X _ _

private def completedLeft (n : ℕ) : pdTerm p W Q.n n →+* (Dc n).carrier := by
  let := WittToSmall.smallWittAlgebra P hpC hlocal Q n
  exact (WittToSmall.mapAt P hpC hlocal Q n).toRingHom.comp
    ((frameInclusion P hpC hlocal Q n).toRingHom.comp
      (PDSmallModelComparison.termEquiv p W γW hpW hkW hpRegW Q.n hw n).toRingHom)

private def completedRight (n : ℕ) : pdTerm p W Q.n n →+* (Dc n).carrier :=
  (PDSmallModelComparison.termEquiv p C γC hp' hk hpC Q.n hc n).toRingHom.comp
    ((pdModelBaseChange p W C Q.n).app ⦋n⦌).right.hom

private theorem completed_square (n : ℕ) :
    completedLeft P hpC hlocal hk Q n = completedRight P hpC hlocal hk Q n := by
  let u := principalCompletionUnitRingHom (pdRaw W Q.n n) (p : pdRaw W Q.n n)
  have hL : (completedLeft P hpC hlocal hk Q n).comp u = rawLeft P hpC hlocal hk Q n := by
    apply RingHom.ext
    intro x
    let := WittToSmall.smallWittAlgebra P hpC hlocal Q n
    change WittToSmall.mapAt P hpC hlocal Q n
      (frameInclusion P hpC hlocal Q n
        (PDSmallModelComparison.termEquiv p W γW hpW hkW hpRegW Q.n hw n (u x))) = _
    rw [PDSmallModelComparison.termEquiv_unit]
    rfl
  have hR : (completedRight P hpC hlocal hk Q n).comp u = rawRight P hpC hlocal hk Q n := by
    apply RingHom.ext
    intro x
    change PDSmallModelComparison.termEquiv p C γC hp' hk hpC Q.n hc n
      (((pdModelBaseChange p W C Q.n).app ⦋n⦌).right (pdModelUnit p W Q.n ⦋n⦌ x)) = _
    rw [pdModelBaseChange_unit]
    exact PDSmallModelComparison.termEquiv_unit p C γC hp' hk hpC Q.n hc n _
  have hcomplete := PDSmallModelComparison.complete_of_ringHom
    (R := pdRaw W Q.n n) (T := (Dc n).carrier) p (rawRight P hpC hlocal hk Q n)
    (Dc n).isEnvelope.complete
  exact (principalCompletion_existsUnique_ringHom _ _ _ _ hcomplete).unique
    (hL.trans (raw_square P hpC hlocal hk Q n)) hR

local notation "resW" => Under.map (CommRingCat.ofHom (wZero p C))
local notation "isoC" => PDPolynomialFunctor.smallIsoNatural p γC hp' hk hpC

private theorem toFinite_eq (n : SimplexCategory) :
    (((wittToSmall P hpC hlocal hk).app Q ≫
      Functor.whiskerRight ((isoC).hom.app Q) resW).app n) =
        (WittToSmall.finiteFrame P hpC hlocal Q).app n := by
  change (((WittToSmall.toFinite P hpC hlocal).app Q ≫
    Functor.whiskerRight ((isoC).inv.app Q) resW) ≫
      Functor.whiskerRight ((isoC).hom.app Q) resW).app n = _
  rw [Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id_app]
  change (((WittToSmall.toFinite P hpC hlocal).app Q) ≫
    Functor.whiskerRight (NatTrans.id ((PDPolynomialFunctor.nerve p γC hp').obj Q)) resW).app n = _
  simp only [Functor.whiskerRight_id, NatTrans.comp_app]
  change (WittToSmall.finiteFrame P hpC hlocal Q).app n ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 大きい Witt 枠を経由する比較は有限枠上で第 0 成分による係数変更に一致する。 -/
theorem _root_.SerrePositivity.BhattScholze.Prismatic.wittToSmall_frame :
    wittSmallFrame P hpC hlocal Q hk ≫ (wittToSmall P hpC hlocal hk).app Q ≫
      Functor.whiskerRight (eqToHom (show
        (pdPolynomialFunctor p γC (Ideal.mem_span_singleton_self (p : C)) hk hpC).obj Q =
          pdModel p C Q.n from by rfl)) resW =
      @pdModelBaseChange _ W C _ _ (wZero p C).toAlgebra Q.n := by
  apply NatTrans.ext
  funext n
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply (PDSmallModelComparison.termEquiv p C γC hp' hk hpC Q.n hc n.len).injective
  have he := RingHom.congr_fun (completed_square P hpC hlocal hk Q n.len) x
  change (((wittSmallFrame P hpC hlocal Q hk).app n).right ≫
    ((((wittToSmall P hpC hlocal hk).app Q) ≫
      Functor.whiskerRight ((isoC).hom.app Q) resW).app n).right)
      x = completedRight P hpC hlocal hk Q n.len x
  rw [toFinite_eq P hpC hlocal hk Q n]
  exact he

end SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame
