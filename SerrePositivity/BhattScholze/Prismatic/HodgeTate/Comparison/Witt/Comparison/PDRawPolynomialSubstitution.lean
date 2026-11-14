module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 未完備の分冪模型での多項式代入

## 概要
小さい分冪模型の各頂点に同じ多項式代入を施す。

## 方針
代入後も頂点差と基底の分冪イデアルは標的の分冪イデアルに入る。
未完備包の普遍性から代入を延長し、各変数上の等式で合成を確かめる。

## 規約
基底は p 正則かつ p 完備。未完備で代入を作るので偏微分との照合に使える。

## 使われ方
BS 著者版 Theorem 6.4 の pd de Rham の自然性。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))

local notation "PD" => PDSmallRawEnvelope.dividedPowers p
local notation "rawIdeal" => PDSmallRawEnvelope.ideal (k := k) (J := J)

variable {Q Q' Q'' : Poly k} (f : Q ⟶ Q')

/-- 多項式を指定した頂点で評価する。 -/
def evalVertex (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin Q.n) k →ₐ[k] pdRaw k Q.n n :=
  MvPolynomial.aeval (fun j => copy k Q.n ⦋n⦌ j i)

private def evalFrame (n : ℕ) :
    pdFrame k (ULift.{u} (Fin Q.n)) n →ₐ[k] pdRaw k Q'.n n :=
  MvPolynomial.aeval fun x => evalVertex (Q := Q') n x.2 (Poly.hom f (MvPolynomial.X x.1.down))

private theorem copy_difference_mem (Q : Poly k) (n : ℕ) (j : Fin Q.n) (i : Fin (n + 1)) :
    copy k Q.n ⦋n⦌ j i - copy k Q.n ⦋n⦌ j 0 ∈ rawIdeal Q.n n := by
  let U := PDSmallRawEnvelope.unit (k := k) Q.n n
  have hx : MvPolynomial.X ((ULift.up j : ULift.{u} (Fin Q.n)), i) -
      MvPolynomial.X (ULift.up j, 0) ∈
      RingHom.ker (pdFrameEval (k := k)
        (fun x : ULift.{u} (Fin Q.n) => (MvPolynomial.X x.down :
          MvPolynomial (Fin Q.n) (k ⧸ J))) n) := by
    apply RingHom.mem_ker.mpr
    rw [map_sub, pdFrameEval_X, pdFrameEval_X, sub_self]
  have h := PDSmallRawEnvelope.unit_map_le (J := J) Q.n n (Ideal.mem_map_of_mem U hx)
  simpa only [U, map_sub, PDSmallRawEnvelope.unit_X] using h

private theorem evalVertex_quotient (Q : Poly k) (n : ℕ) (i : Fin (n + 1)) :
    (Ideal.Quotient.mkₐ k (rawIdeal Q.n n)).comp (evalVertex (Q := Q) n i) =
      (Ideal.Quotient.mkₐ k (rawIdeal Q.n n)).comp (evalVertex (Q := Q) n 0) := by
  apply MvPolynomial.algHom_ext
  intro j
  change Ideal.Quotient.mk _ (evalVertex (Q := Q) n i (MvPolynomial.X j)) =
    Ideal.Quotient.mk _ (evalVertex (Q := Q) n 0 (MvPolynomial.X j))
  simp only [evalVertex, MvPolynomial.aeval_X]
  exact Ideal.Quotient.eq.mpr (copy_difference_mem (J := J) Q n j i)

private theorem evalFrame_ideal (n : ℕ) :
    (RingHom.ker (pdFrameEval (k := k)
      (fun x : ULift.{u} (Fin Q.n) => (MvPolynomial.X x.down :
        MvPolynomial (Fin Q.n) (k ⧸ J))) n)).map (evalFrame f n) ≤ rawIdeal Q'.n n := by
  let q := Ideal.Quotient.mkₐ k (rawIdeal Q'.n n)
  let E := q.comp (evalFrame f n)
  have hb (x : k) (hx : x ∈ J) :
      algebraMap k (pdRaw k Q'.n n ⧸ rawIdeal Q'.n n) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (PDRelativeFree.coefficient_mem _ _ hx)
  have hv (j : ULift.{u} (Fin Q.n)) (i : Fin (n + 1)) :
      E (MvPolynomial.X (j, i)) = E (MvPolynomial.X (j, 0)) := by
    simp only [E, AlgHom.comp_apply, evalFrame, MvPolynomial.aeval_X]
    exact DFunLike.congr_fun (evalVertex_quotient (J := J) Q' n i) (Poly.hom f (MvPolynomial.X j.down))
  have h := PDSmallRawEnvelope.kernel_le (J := J) Q.n n E hb hv
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change evalFrame f n x ∈ rawIdeal Q'.n n
  exact Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp (h hx))

private theorem existsUnique_substitute (n : ℕ) :
    ∃! a : pdRaw k Q.n n →ₐ[k] pdRaw k Q'.n n,
      (PD Q.n n γ hk hr).IsDPMorphism (PD Q'.n n γ hk hr) a.toRingHom ∧
        a.comp (PDSmallRawEnvelope.unit Q.n n) = evalFrame f n :=
  (PDSmallRawEnvelope.isRelativePDEnvelope p Q.n n γ hk hr).lift
    (PD Q'.n n γ hk hr) (evalFrame f n) (evalFrame_ideal (J := J) f n)
      (PDSmallRawEnvelope.isRelativePDEnvelope p Q'.n n γ hk hr).base_dp

/-- 未完備の分冪模型の多項式代入。 -/
def substitute (n : ℕ) : pdRaw k Q.n n →ₐ[k] pdRaw k Q'.n n :=
  (existsUnique_substitute p γ hk hr f n).choose

theorem substitute_isDPMorphism (n : ℕ) :
    (PD Q.n n γ hk hr).IsDPMorphism (PD Q'.n n γ hk hr)
      (substitute p γ hk hr f n).toRingHom :=
  (existsUnique_substitute p γ hk hr f n).choose_spec.1.1

/-- 代入は各頂点の変数をその頂点での指定された多項式の評価に送る。 -/
private theorem substitute_copy (n : ℕ) (j : Fin Q.n) (i : Fin (n + 1)) :
    substitute p γ hk hr f n (copy k Q.n ⦋n⦌ j i) =
      evalVertex (Q := Q') n i (Poly.hom f (MvPolynomial.X j)) := by
  have h := (existsUnique_substitute p γ hk hr f n).choose_spec.1.2
  have he := DFunLike.congr_fun h (MvPolynomial.X ((ULift.up j : ULift.{u} (Fin Q.n)), i))
  simpa only [substitute, AlgHom.comp_apply, PDSmallRawEnvelope.unit_X, evalFrame,
    MvPolynomial.aeval_X] using he

private theorem substitute_vertex (n : ℕ) (i : Fin (n + 1)) :
    (substitute p γ hk hr f n).comp (evalVertex (Q := Q) n i) =
      (evalVertex (Q := Q') n i).comp (Poly.hom f) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, evalVertex, MvPolynomial.aeval_X]
  exact substitute_copy p γ hk hr f n j i

/-- 代入と頂点の写像は可換。 -/
private theorem substitute_naturality {m n : SimplexCategory} (θ : m ⟶ n) :
    (substitute p γ hk hr f n.len).comp (pdRawMap k Q.n θ) =
      (pdRawMap k Q'.n θ).comp (substitute p γ hk hr f m.len) := by
  apply PDSmallRawEnvelope.hom_ext p Q.n m.len γ hk hr (PD Q'.n n.len γ hk hr)
    ((substitute_isDPMorphism p γ hk hr f n.len).comp _
      (PDSmallRawEnvelope.map_isDPMorphism p Q.n γ hk hr θ))
    ((PDSmallRawEnvelope.map_isDPMorphism p Q'.n γ hk hr θ).comp _
      (substitute_isDPMorphism p γ hk hr f m.len))
  apply MvPolynomial.algHom_ext
  rintro ⟨j, i⟩
  simp only [AlgHom.comp_apply, PDSmallRawEnvelope.unit_X, pdRawMap_copy, substitute_copy]
  have h : (pdRawMap k Q'.n θ).comp (evalVertex (Q := Q') m.len i) =
      evalVertex (Q := Q') n.len (θ.toOrderHom i) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, evalVertex, MvPolynomial.aeval_X, pdRawMap_copy]
  exact (substitute_copy p γ hk hr f n.len j.down (θ.toOrderHom i)).trans
    (DFunLike.congr_fun h (Poly.hom f (MvPolynomial.X j.down))).symm

/-- 恒等代入。 -/
theorem substitute_id (Q : Poly k) (n : ℕ) :
    substitute p γ hk hr (𝟙 Q) n = AlgHom.id k _ := by
  apply PDSmallRawEnvelope.hom_ext p Q.n n γ hk hr (PD Q.n n γ hk hr)
    (substitute_isDPMorphism p γ hk hr (𝟙 Q) n)
    (DividedPowers.DPMorphism.id (PD Q.n n γ hk hr)).isDPMorphism
  apply MvPolynomial.algHom_ext
  rintro ⟨j, i⟩
  simp only [AlgHom.comp_apply, PDSmallRawEnvelope.unit_X, substitute_copy, AlgHom.id_apply]
  exact MvPolynomial.aeval_X _ _

/-- 多項式代入の合成。 -/
theorem substitute_comp (g : Q' ⟶ Q'') (n : ℕ) :
    substitute p γ hk hr (f ≫ g) n = (substitute p γ hk hr g n).comp (substitute p γ hk hr f n) := by
  apply PDSmallRawEnvelope.hom_ext p Q.n n γ hk hr (PD Q''.n n γ hk hr)
    (substitute_isDPMorphism p γ hk hr (f ≫ g) n)
    ((substitute_isDPMorphism p γ hk hr g n).comp _ (substitute_isDPMorphism p γ hk hr f n))
  apply MvPolynomial.algHom_ext
  rintro ⟨j, i⟩
  simp only [AlgHom.comp_apply, PDSmallRawEnvelope.unit_X, substitute_copy]
  exact (DFunLike.congr_fun (substitute_vertex p γ hk hr g n i)
    (Poly.hom f (MvPolynomial.X j.down))).symm

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
