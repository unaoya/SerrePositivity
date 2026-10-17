module

public import SerrePositivity.BhattScholze.Andre.PrimeAdicCompletionPrincipalQuotient

/-!
# André A1-a：全冪商で正則な主関係と p 完備化の交換

## 概要

入力 g が全 p 冪商で正則なら、p 完備化を g で割る操作と g 商を p 完備化する操作は
元の係数射を保つ環同型で結ばれる。BS Rem 7.15（著者版 p.62）の完備入力環。

## 方針

完備化後の主商の完備性を証明済みの一様な比較から得る。
両方向の射を完備化と商の普遍性で構成し、一意性で互いに逆と示す。
原典の記述を補う環射の普遍性による経路。

## 規約

元の環の p 正則性や有界ねじれは要求せず、全冪商の g 正則性だけを仮定する。

## 使われ方

モニック無限根入力に適用して、原典の完備多項式商を既存の完備入力へ接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R] (p : ℕ) (g : R)
local notation "C" => AdicCompletion (Ideal.span {(p : R)}) R
local notation "j" => algebraMap R C
local notation "S" => R ⧸ Ideal.span {(g : R)}
local notation "q" => Ideal.Quotient.mk (Ideal.span {(g : R)})
local notation "CS" => AdicCompletion (Ideal.span {(p : S)}) S
local notation "jS" => algebraMap S CS
local notation "Z" => C ⧸ Ideal.span {j g}
local notation "qC" => Ideal.Quotient.mk (Ideal.span {j g})
variable (hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {(p : R) ^ n})
  (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) g))

include hg in
/-- 概要：全冪商で正則な主関係は p 完備化と係数射を保って交換する。
方針：両側の完備性と二つの普遍性で往復射を作り、その合成を元の環上で確認する。
規約：元の主商と通常の p 完備化を使う。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力環の同定。 -/
theorem exists_primeAdicCompletionQuotientEquiv :
    ∃ e : Z ≃+* CS, e.toRingHom.comp ((qC).comp j) = (jS).comp q := by
  let := primeAdicCompletion_isAdicComplete S p
  let := primeAdicCompletion_principal_quotient_isAdicComplete R p g hg
  obtain ⟨F₀, hF₀, _⟩ := existsUnique_primeAdicCompletionHom R p ((jS).comp q)
  have hF₀g : F₀ (j g) = 0 := by
    have h := RingHom.congr_fun hF₀ g
    simpa only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self g), map_zero] using h
  let F : Z →+* CS := Ideal.Quotient.lift _ F₀ (by
    change Ideal.span {j g} ≤ RingHom.ker F₀
    exact Ideal.span_le.mpr (fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hF₀g))
  let r : S →+* Z := Ideal.Quotient.lift _ ((qC).comp j) (by
    change Ideal.span {(g : R)} ≤ RingHom.ker ((qC).comp j)
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  obtain ⟨G, hG, _⟩ := existsUnique_primeAdicCompletionHom S p r
  have hGF : G.comp F = RingHom.id Z := by
    apply Ideal.Quotient.ringHom_ext
    apply primeAdicCompletion_ringHom_ext R p
    apply RingHom.ext
    intro x
    change G (F₀ (j x)) = qC (j x)
    rw [show F₀ (j x) = jS (q x) from RingHom.congr_fun hF₀ x]
    exact RingHom.congr_fun hG (q x)
  have hFG : F.comp G = RingHom.id CS := by
    apply primeAdicCompletion_ringHom_ext S p
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change F (G (jS (q a))) = jS (q a)
    rw [show G (jS (q a)) = r (q a) from RingHom.congr_fun hG (q a)]
    exact RingHom.congr_fun hF₀ a
  let e : Z ≃+* CS := { F with
    invFun := G
    left_inv := RingHom.congr_fun hGF
    right_inv := RingHom.congr_fun hFG }
  refine ⟨e, ?_⟩
  apply RingHom.ext
  exact RingHom.congr_fun hF₀

/-- 概要：全冪商で正則な主関係と p 完備化を交換する具体的な環同型。
方針：係数射を保つ同型の存在定理から一つ選ぶ。
規約：後続の係数公式で選択に依存しない入力作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力の比較射。 -/
def primeAdicCompletionQuotientEquiv : Z ≃+* CS :=
  (exists_primeAdicCompletionQuotientEquiv R p g hg).choose

/-- 概要：完備化と主商の交換同型は元の全係数元を保つ。
方針：選んだ同型が満たす環射の合成等式を各元に適用する。
規約：根変数の像を含め、元の環全体で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の入力根の作用を追跡する。 -/
theorem primeAdicCompletionQuotientEquiv_coeff (x : R) :
    primeAdicCompletionQuotientEquiv R p g hg (qC (j x)) = jS (q x) :=
  RingHom.congr_fun (exists_primeAdicCompletionQuotientEquiv R p g hg).choose_spec x

end SerrePositivity.BhattScholze.Andre
