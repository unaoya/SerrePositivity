module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDPolynomialSplitEnvelope
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison

/-!
# 多項式グラフの分冪包

## 概要
剰余評価の余分な座標が、多項式変数で表されたグラフの場合の比較。

## 方針
左の座標を固定し、右の座標から指定された多項式を引く。
この座標変換で、余分な座標を零へ送る評価に帰着する。

## 規約
余分な座標の多項式には基底上の持ち上げを使う。

## 使われ方
BS 著者版 Theorem 6.4 の大きい分冪枠の p 正則性。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDPolynomialGraph

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] {J : Ideal k}
variable {α σ τ : Type u}
variable (e : α ⊕ σ ≃ τ) (q : σ → MvPolynomial α k)

local notation "F" => MvPolynomial (α ⊕ σ) k
local notation "Lft" => MvPolynomial.rename (R := k) (Sum.inl : α → α ⊕ σ)

private def shiftHom (sgn : ℤ) : F →ₐ[k] F :=
  MvPolynomial.aeval (Sum.elim (MvPolynomial.X ∘ Sum.inl)
    (fun j => MvPolynomial.X (Sum.inr j) + sgn • Lft (q j)))

private theorem shiftHom_left (sgn : ℤ) :
    (shiftHom q sgn).comp Lft = Lft := by
  apply MvPolynomial.algHom_ext
  intro i
  change shiftHom q sgn (MvPolynomial.rename Sum.inl (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X, shiftHom, MvPolynomial.aeval_X]
  rfl

private theorem shiftHom_inv (sgn : ℤ) :
    (shiftHom q (-sgn)).comp (shiftHom q sgn) = AlgHom.id k F := by
  apply MvPolynomial.algHom_ext
  intro x
  change shiftHom q (-sgn) (shiftHom q sgn (MvPolynomial.X x)) = MvPolynomial.X x
  cases x with
  | inl i => simp [shiftHom]
  | inr j =>
    have h := DFunLike.congr_fun (shiftHom_left q (-sgn)) (q j)
    change shiftHom q (-sgn) (Lft (q j)) = Lft (q j) at h
    rw [show shiftHom q sgn (MvPolynomial.X (Sum.inr j)) =
      MvPolynomial.X (Sum.inr j) + sgn • Lft (q j) from MvPolynomial.aeval_X _ _,
      map_add, map_zsmul, h]
    rw [show shiftHom q (-sgn) (MvPolynomial.X (Sum.inr j)) =
      MvPolynomial.X (Sum.inr j) + (-sgn) • Lft (q j) from MvPolynomial.aeval_X _ _]
    simp

/-- 右の変数を持ち上げた多項式だけ平行移動する。 -/
def shift : F ≃ₐ[k] F :=
  AlgEquiv.ofAlgHom (shiftHom q 1) (shiftHom q (-1))
    (by simpa only [neg_neg] using shiftHom_inv q (-1)) (shiftHom_inv q 1)

/-- 元の座標から、余分な座標を零とする座標への変換。 -/
def toSplit : MvPolynomial τ k ≃ₐ[k] F :=
  (MvPolynomial.renameEquiv k e.symm).trans (shift q)

variable (v : MvPolynomial τ k →ₐ[k] MvPolynomial α (k ⧸ J))
variable (hleft : ∀ i, v (MvPolynomial.X (e (Sum.inl i))) = MvPolynomial.X i)
variable (hright : ∀ j, v (MvPolynomial.X (e (Sum.inr j))) =
  MvPolynomial.map (Ideal.Quotient.mk J) (q j))

include hleft hright in
/-- 元の剰余評価は座標変換に続けて右の変数を零にする評価。 -/
theorem evaluate_toSplit :
    (PDPolynomialSplitEnvelope.evaluate (J := J) α σ).comp (toSplit e q).toAlgHom = v := by
  have h : (PDPolynomialSplitEnvelope.evaluate (J := J) α σ).comp Lft =
      MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ k J) := by
    apply MvPolynomial.algHom_ext
    intro i
    change PDPolynomialSplitEnvelope.evaluate (J := J) α σ
      (MvPolynomial.rename Sum.inl (MvPolynomial.X i)) =
        MvPolynomial.map (Ideal.Quotient.mk J) (MvPolynomial.X i)
    rw [MvPolynomial.rename_X, PDPolynomialSplitEnvelope.evaluate_X_inl, MvPolynomial.map_X]
  apply MvPolynomial.algHom_ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  change PDPolynomialSplitEnvelope.evaluate (J := J) α σ
    (shiftHom q 1 (MvPolynomial.rename e.symm (MvPolynomial.X (e x)))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply, shiftHom, MvPolynomial.aeval_X]
  cases x with
  | inl i =>
    change PDPolynomialSplitEnvelope.evaluate (J := J) α σ (MvPolynomial.X (Sum.inl i)) = _
    rw [PDPolynomialSplitEnvelope.evaluate_X_inl, hleft]
  | inr j =>
    change PDPolynomialSplitEnvelope.evaluate (J := J) α σ
      (MvPolynomial.X (Sum.inr j) + 1 • Lft (q j)) = _
    rw [one_zsmul, map_add, PDPolynomialSplitEnvelope.evaluate_X_inr, zero_add, hright]
    exact DFunLike.congr_fun h (q j)

private theorem map_kernel (h : (PDPolynomialSplitEnvelope.evaluate (J := J) α σ).comp
    (toSplit e q).toAlgHom = v) :
    (RingHom.ker v.toRingHom).map (toSplit e q).toRingHom =
      RingHom.ker (PDPolynomialSplitEnvelope.evaluate (J := J) α σ).toRingHom := by
  change (RingHom.ker v).map (toSplit e q).toAlgHom = _
  rw [← h, ← AlgHom.comap_ker]
  exact Ideal.map_comap_of_surjective _ (toSplit e q).surjective _

open PDPolynomialSplitEnvelope in
private theorem graph_isRelativePDEnvelope (p : ℕ) [Fact p.Prime] (γ : DividedPowers J)
    (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
    (hreg : Function.Injective (fun x : k => (p : k) * x))
    (h : (PDPolynomialSplitEnvelope.evaluate (J := J) α σ).comp (toSplit e q).toAlgHom = v) :
    IsRelativePDEnvelope γ (RingHom.ker v.toRingHom) (D := Raw (k := k) α σ)
      (dividedPowers α σ p γ hk hreg)
      ((unit α σ).comp (toSplit e q).toAlgHom) := by
  let T := toSplit e q
  let H := isRelativePDEnvelope α σ p γ hk hreg
  refine ⟨?_, H.base_dp, ?_⟩
  · change Ideal.map ((unit (k := k) α σ).toRingHom.comp (toSplit e q).toRingHom)
      (RingHom.ker v.toRingHom) ≤ PDRelativeFree.ideal (MvPolynomial α k) σ J
    rw [← Ideal.map_map, map_kernel e q v h]
    exact H.map_le
  intro E _ _ I ε g hg hγ
  let g' := g.comp T.symm.toAlgHom
  have hm : (RingHom.ker (evaluate (J := J) α σ).toRingHom).map g' ≤ I := by
    change (RingHom.ker (evaluate (J := J) α σ).toRingHom).map g'.toRingHom ≤ I
    rw [← map_kernel e q v h, Ideal.map_map]
    have he : g'.toRingHom.comp T.toRingHom = g.toRingHom := RingHom.ext fun x => by
      change g (T.symm (T x)) = g x
      rw [T.symm_apply_apply]
    rwa [he]
  obtain ⟨f, ⟨hf, hf'⟩, hu⟩ := H.lift ε g' hm hγ
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · apply AlgHom.ext
    intro x
    have hfx := DFunLike.congr_fun hf' (T x)
    change f (unit α σ (T x)) = g (T.symm (T x)) at hfx
    rwa [T.symm_apply_apply] at hfx
  intro f' hf'
  apply hu f'
  refine ⟨hf'.1, ?_⟩
  apply AlgHom.ext
  intro x
  have hfx := DFunLike.congr_fun hf'.2 (T.symm x)
  change f' (unit α σ (T (T.symm x))) = g (T.symm x) at hfx
  rwa [T.apply_symm_apply] at hfx

open SerrePositivity.DerivedCompletion in
private theorem adic_regular {R : Type u} [CommRing R] (p : ℕ) (h : IsSMulRegular R (p : R)) :
    Function.Injective (fun x : AdicCompletion (Ideal.span {(p : R)}) R => (p : _) * x) := by
  let := principalCompletionCommRing R (p : R)
  let := principalCompletionAlgebra R (p : R)
  let E := principalCompletionAdicAlgEquiv R (p : R) h
  intro x y hxy
  apply E.symm.injective
  apply principalCompletionH0_smul_injective_of_regular R (p : R) h
  change (p : R) • E.symm x = (p : R) • E.symm y
  change (p : AdicCompletion (Ideal.span {(p : R)}) R) * x = _ at hxy
  simpa only [Algebra.smul_def, map_natCast, map_mul] using congrArg E.symm hxy

open PDPolynomialSplitEnvelope in
include hleft hright in
/-- p 正則な基底上のグラフ評価の完備分冪包は p 正則。 -/
theorem completed_regular (p : ℕ) [Fact p.Prime] (γ : DividedPowers J)
    (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
    (hreg : Function.Injective (fun x : k => (p : k) * x))
    (hp : (p : k) ∈ J) {K : Ideal (MvPolynomial τ k)} (hK : K = RingHom.ker v.toRingHom)
    (D : CompletedPDEnvelopeData p γ K) :
    Function.Injective (fun x : D.carrier => (p : D.carrier) * x) := by
  have hr : IsRelativePDEnvelope γ K (D := Raw (k := k) α σ) (dividedPowers α σ p γ hk hreg)
      ((unit α σ).comp (toSplit e q).toAlgHom) := by
    rw [hK]
    exact graph_isRelativePDEnvelope e q v p γ hk hreg (evaluate_toSplit e q v hleft hright)
  let h := hr.complete p hp
  let E := h.equiv D.isEnvelope
  intro x y hxy
  apply E.symm.injective
  apply adic_regular p (raw_regular α σ p hreg)
  simpa only [map_mul, map_natCast] using congrArg E.symm hxy

end SerrePositivity.BhattScholze.Prismatic.PDPolynomialGraph
