module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialGraph
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
public import Mathlib.Logic.Equiv.Set
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame

/-!
# 大きい Witt 分冪模型の結晶 prism

## 概要
大きい分冪 Čech 脈体の各項は p 正則であり、結晶 prism の構造を持つ。

## 方針
第 0 頂点の通常の多項式変数を残し、残りの変数を剰余における評価の持ち上げで平行移動する。
これにより分冪包は自由分冪代数を含むグラフの模型で計算できる。

## 規約
座標の選択は p 正則性の証明だけに使う。結晶 prism の台環は元の分冪包。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋の標的。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittBigCrystalline

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "Jw" => wittPdIdeal p C
local notation "Ic" => Ideal.span {(p : C)}

local instance : Algebra W C := (wZero p C).toAlgebra

variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (Q : Poly (A ⧸ P.ideal)) (n : ℕ)

private abbrev vars (Q : Poly C) := ULift.{u} (Fin Q.n)

local notation "V" => vars P Q
local notation "S" => polyCompletion P Q.n × Fin (n + 1)
local notation "γ" => wittPdStructure p C hpC hlocal
local notation "hpW" => p_mem_wittPdIdeal p C

private theorem baseKer : Jw ≤ RingHom.ker (algebraMap W (bigResidue P Q)) :=
  bigResidue_ker P (J := Jw) le_rfl Q

local notation "s" => (Ideal.Quotient.mk (Ideal.span {(p : polyCompletion P Q.n)}))

/-- 大きい Witt 分冪脈体の各項の完備分冪包。 -/
def term : CompletedPDEnvelopeData p γ (RingHom.ker (pdFrameEval (k := W) s n)) :=
  PDCechNerve.term p γ hpW (baseKer P Q) s n

private def anchor (j : V) : S :=
  (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j.down), 0)

private def residueIso : MvPolynomial V (W ⧸ Jw) ≃ₐ[W] bigResidue P Q :=
  ((MvPolynomial.renameEquiv (W ⧸ Jw) Equiv.ulift).restrictScalars W).trans
    (smallResidueEquiv P hpC Q)

private theorem residueIso_X (j : V) :
    residueIso P hpC Q (MvPolynomial.X j) = s (anchor P Q n j).1 := by
  change smallResidueEquiv P hpC Q (MvPolynomial.rename ULift.down (MvPolynomial.X j)) =
    s (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j.down))
  rw [MvPolynomial.rename_X]
  exact smallResidueEquiv_X P hpC Q j.down

include hpC in
private theorem anchor_injective [Nontrivial (W ⧸ Jw)] :
    Function.Injective (anchor P Q n) := by
  intro i j h
  apply MvPolynomial.X_injective (R := W ⧸ Jw)
  apply (residueIso P hpC Q).injective
  rw [residueIso_X, residueIso_X]
  exact congrArg (fun x : S => s x.1) h

private def other := ((Set.range (anchor P Q n))ᶜ : Set S)

private def indices [Nontrivial (W ⧸ Jw)] : V ⊕ (other P Q n) ≃ S := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective (anchor P Q n) (anchor_injective P hpC Q n))
    (Equiv.refl _)).trans (Equiv.Set.sumCompl _)

private theorem indices_left [Nontrivial (W ⧸ Jw)] (i : V) :
    indices P hpC Q n (Sum.inl i) = anchor P Q n i := by
  classical
  rfl

private def evaluate : MvPolynomial S W →ₐ[W] MvPolynomial V (W ⧸ Jw) :=
  (residueIso P hpC Q).symm.toAlgHom.comp (pdFrameEval (k := W) s n)

private theorem evaluate_ker :
    RingHom.ker (evaluate P hpC Q n).toRingHom = RingHom.ker (pdFrameEval (k := W) s n).toRingHom :=
  RingHom.ker_comp_of_injective _ (residueIso P hpC Q).symm.injective

private theorem evaluate_left [Nontrivial (W ⧸ Jw)] (i : V) :
    evaluate P hpC Q n (MvPolynomial.X (indices P hpC Q n (Sum.inl i))) = MvPolynomial.X i := by
  apply (residueIso P hpC Q).injective
  rw [indices_left, residueIso_X P hpC Q n i]
  change residueIso P hpC Q ((residueIso P hpC Q).symm (pdFrameEval (k := W) s n
    (MvPolynomial.X (anchor P Q n i)))) = _
  rw [AlgEquiv.apply_symm_apply, pdFrameEval_X]

private def rightLift [Nontrivial (W ⧸ Jw)] (j : other P Q n) : MvPolynomial V W :=
  (MvPolynomial.map_surjective (Ideal.Quotient.mk Jw) Ideal.Quotient.mk_surjective
    (evaluate P hpC Q n (MvPolynomial.X (indices P hpC Q n (Sum.inr j))))).choose

private theorem rightLift_spec [Nontrivial (W ⧸ Jw)] (j : other P Q n) :
    evaluate P hpC Q n (MvPolynomial.X (indices P hpC Q n (Sum.inr j))) =
      MvPolynomial.map (Ideal.Quotient.mk Jw) (rightLift P hpC Q n j) := by
  let h := MvPolynomial.map_surjective (Ideal.Quotient.mk Jw) Ideal.Quotient.mk_surjective
    (evaluate P hpC Q n (MvPolynomial.X (indices P hpC Q n (Sum.inr j))))
  exact h.choose_spec.symm

variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]

/-- 大きい Witt 分冪枠の各項は p 正則。 -/
theorem regular :
    Function.Injective (fun x : (term P hpC hlocal Q n).carrier =>
      (p : (term P hpC hlocal Q n).carrier) * x) := by
  rcases subsingleton_or_nontrivial C with h | h
  · let : Subsingleton W := ⟨fun x y => WittVector.ext (fun _ => Subsingleton.elim _ _)⟩
    let := Algebra.subsingleton W (term P hpC hlocal Q n).carrier
    exact fun _ _ _ => Subsingleton.elim _ _
  have hI : Ic ≠ ⊤ := by
    intro htop
    have hj : Ic ≤ Ideal.jacobson (⊥ : Ideal C) := IsAdicComplete.le_jacobson_bot Ic
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp (top_le_iff.mp (htop ▸ hj)))
  let : Nontrivial (C ⧸ Ic) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : Nontrivial (W ⧸ Jw) := (wittResidueEquiv P).symm.injective.nontrivial
  let hW : IsAdicComplete (Ideal.span {(p : W)}) W := witt_isAdicComplete p C hpC
  exact PDPolynomialGraph.completed_regular (indices P hpC Q n) (rightLift P hpC Q n)
    (evaluate P hpC Q n) (evaluate_left P hpC Q n) (rightLift_spec P hpC Q n) p γ hW
    (witt_mul_prime_injective p C hpC) hpW (evaluate_ker P hpC Q n).symm
    (term P hpC hlocal Q n)

/-- 大きい Witt 分冪枠の各項の結晶 prism。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.wittBigCrystalline :
    OrientedPrism p (term P hpC hlocal Q n).carrier :=
  wittPDEnvelopeCrystalline hpC hlocal (term P hpC hlocal Q n) (regular P hpC hlocal Q n)

end SerrePositivity.BhattScholze.Prismatic.WittBigCrystalline
