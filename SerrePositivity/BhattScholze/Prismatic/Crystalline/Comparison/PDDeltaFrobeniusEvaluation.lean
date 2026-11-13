module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
public import SerrePositivity.BhattScholze.Delta.Division.Basic
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# Frobenius 差の δ 除算模型から分冪包への評価

## 概要
Frobenius を施した頂点差を p で割る完備 δ 模型を、小さい分冪包へ写す。

## 方針
自由 δ 環の変数を枠の変数へ評価する。
分冪イデアルの Frobenius 像が (p) に含まれることから、δ 除算の普遍性を適用する。

## 規約
基底 prism の生成元は p。分冪包の p 正則性と頂点差の分冪イデアルへの所属を仮定する。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の小さい模型への結晶比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k]
variable (P : OrientedPrism p k) (r n : ℕ)

/-- 各頂点の第 0 頂点との差に Frobenius を施した元。 -/
def pdFrobeniusDifference (s : ULift.{u} (Fin r × Fin n)) :
    completedFreeDelta P (AffineIndex r n) :=
  (completedFreeDeltaStructure P (AffineIndex r n)).frobeniusLift
    (affineVariable P r n s.down.1 s.down.2.succ - affineVariable P r n s.down.1 0)

variable {J : Ideal k} (γ : DividedPowers J)
variable {K : Ideal (MvPolynomial (ULift.{u} (Fin r) × Fin (n + 1)) k)}
variable (E : CompletedPDEnvelopeData p γ K)
variable (hreg : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : k))
variable (hφ : J.map P.deltaStructure.frobeniusLift ≤ Ideal.span {(p : k)})
variable (hgen : P.generator = p)

include hgen

local notation "Src" => completedFreeDelta P (AffineIndex r n)
local notation "D" => completedFreeDeltaStructure P (AffineIndex r n)
local notation "b" => completedFreeDeltaBase P (AffineIndex r n)
local notation "Q" => pdEnvelopeCrystalline P.deltaStructure γ E hreg hlocal hφ
local notation "a" => pdFrobeniusDifference P r n
local notation "Unit" => classicalDeltaDivisionMap D (p : Src) a
local notation "Div" => ClassicalDeltaDivisionCompletion D (p : Src) a

private def value (s : AffineIndex.{u} r n) : E.carrier :=
  E.unit (MvPolynomial.X (ULift.up s.down.1, s.down.2))

private theorem evaluation_existsUnique :
    ∃! f : Src →+* E.carrier,
      (D).IsDeltaHom (Q).deltaStructure f ∧ f.comp b = algebraMap k E.carrier ∧
      ∀ s, f (completedFreeDeltaVariable P (AffineIndex r n) s) = value r n γ E s := by
  have hd : IsModuleComplete E.carrier ((algebraMap k E.carrier) P.generator)
      (ModuleCat.of E.carrier E.carrier) := by
    rw [hgen, map_natCast]
    exact (Q).complete_p
  exact existsUnique_completedFreeDeltaHom P (AffineIndex r n) (Q).deltaStructure
    (algebraMap k E.carrier) (pdEnvelopeCrystalline_base P.deltaStructure γ E hreg hlocal hφ)
    (Q).complete_p hd (value r n γ E)

private def evaluation : Src →+* E.carrier :=
  (evaluation_existsUnique P r n γ E hreg hlocal hφ hgen).choose

private theorem evaluation_spec :
    (D).IsDeltaHom (Q).deltaStructure (evaluation P r n γ E hreg hlocal hφ hgen) ∧
      (evaluation P r n γ E hreg hlocal hφ hgen).comp b = algebraMap k E.carrier ∧
      ∀ s, evaluation P r n γ E hreg hlocal hφ hgen
        (completedFreeDeltaVariable P (AffineIndex r n) s) = value r n γ E s :=
  (evaluation_existsUnique P r n γ E hreg hlocal hφ hgen).choose_spec.1

variable (hdiff : ∀ j : Fin r, ∀ i : Fin (n + 1),
  E.unit (MvPolynomial.X (ULift.up j, i)) -
    E.unit (MvPolynomial.X (ULift.up j, 0)) ∈ E.ideal)

include hdiff in
private theorem division_existsUnique :
    ∃! g : Div →+* E.carrier,
      (classicalDeltaDivisionStructure D (p : Src) a).IsDeltaHom (Q).deltaStructure g ∧
      g.comp Unit = evaluation P r n γ E hreg hlocal hφ hgen := by
  let f := evaluation P r n γ E hreg hlocal hφ hgen
  have hf := evaluation_spec P r n γ E hreg hlocal hφ hgen
  have hp : f (p : Src) = (p : E.carrier) := map_natCast f p
  have hd : Function.Injective (fun x : E.carrier => f (p : Src) * x) := by
    rw [hp]
    exact hreg
  have hdiv (s : ULift.{u} (Fin r × Fin n)) : f (p : Src) ∣ f (a s) := by
    rw [hp]
    apply Ideal.mem_span_singleton.mp
    have hF := (exists_deltaStructure_of_pdPolynomial P.deltaStructure γ E
      hreg hlocal hφ).choose_spec.2.2
    have h := hF.ideal_comp (Ideal.mem_map_of_mem _ (hdiff s.down.1 s.down.2.succ))
    have hx (j : Fin r) (i : Fin (n + 1)) :
        f (affineVariable P r n j i) = E.unit (MvPolynomial.X (ULift.up j, i)) :=
      hf.2.2 ⟨(j,i)⟩
    change f ((D).frobeniusLift
      (affineVariable P r n s.down.1 s.down.2.succ - affineVariable P r n s.down.1 0)) ∈ _
    rw [hf.1.map_frobeniusLift, map_sub, hx, hx]
    exact h
  let := E.isEnvelope.complete
  exact existsUnique_classicalDeltaDivisionHom D (Q).deltaStructure (p : Src) a f hf.1 hd hdiv
    (Ideal.span {(p : E.carrier)}) (Ideal.subset_span rfl)
    (by rw [hp]; exact Ideal.subset_span rfl)

include hdiff

/-- 小さい分冪包への標準の δ 除算評価。 -/
def pdFrobeniusDivisionEvaluation : Div →+* E.carrier :=
  (division_existsUnique P r n γ E hreg hlocal hφ hgen hdiff).choose

/-- δ 除算評価は結晶 δ 構造を保つ。 -/
theorem pdFrobeniusDivisionEvaluation_isDeltaHom :
    (classicalDeltaDivisionStructure D (p : Src) a).IsDeltaHom (Q).deltaStructure
      (pdFrobeniusDivisionEvaluation P r n γ E hreg hlocal hφ hgen hdiff) :=
  (division_existsUnique P r n γ E hreg hlocal hφ hgen hdiff).choose_spec.1.1

/-- δ 除算評価の基底上での像。 -/
theorem pdFrobeniusDivisionEvaluation_base :
    ((pdFrobeniusDivisionEvaluation P r n γ E hreg hlocal hφ hgen hdiff).comp Unit).comp b =
      algebraMap k E.carrier := by
  change ((division_existsUnique P r n γ E hreg hlocal hφ hgen hdiff).choose.comp Unit).comp b = _
  rw [(division_existsUnique P r n γ E hreg hlocal hφ hgen hdiff).choose_spec.1.2]
  exact (evaluation_spec P r n γ E hreg hlocal hφ hgen).2.1

/-- 除算評価の標準脚上での変数像。 -/
theorem pdFrobeniusDivisionEvaluation_variable (j : Fin r) (i : Fin (n + 1)) :
    pdFrobeniusDivisionEvaluation P r n γ E hreg hlocal hφ hgen hdiff
      (Unit (affineVariable P r n j i)) = E.unit (MvPolynomial.X (ULift.up j, i)) := by
  have h := RingHom.congr_fun
    (division_existsUnique P r n γ E hreg hlocal hφ hgen hdiff).choose_spec.1.2
      (affineVariable P r n j i)
  exact h.trans ((evaluation_spec P r n γ E hreg hlocal hφ hgen).2.2 ⟨(j,i)⟩)

end SerrePositivity.BhattScholze.Prismatic
