module

public import SerrePositivity.BhattScholze.Andre.Remark715.DividedPowerPrimeFinitePresentation
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# André E1・E2：一元分冪代数の可算切断多項式表示

## 概要

p が零となる可換係数環上の一元分冪代数は、変数 i を γₚⁱ に送る射により
可算切断多項式商 A[g₀,g₁,…]/(gᵢᵖ) と同型である。
BS Rem 7.15(1)（著者版 p.62）の明示的な表示の自由分冪代数側。

## 方針

任意の多項式は有限個の初期変数から来る。有限切断評価の単射性と、
既に証明した可算評価の全射性を組み合わせる。

## 規約

p は素数で A 内で零。γ₁=f の商や実 pd 包の普遍性は別途必要である。

## 使われ方

γ₁=f を課した商を係数商と残りの切断変数に分離する計算へ進む。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ)
local notation "Q" => DividedPowerPrimeTruncatedAlgebra (A := A) p

/-- 概要：有限初期変数の切断商を可算切断商へ送る標準射。
方針：有限変数を自然数番号へ名前変更する多項式射を関係式商へ降ろす。
規約：標数や素数性はこの射には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限支持からの比較。 -/
def dividedPowerPrimeFiniteToCountable (n : ℕ) :
    DividedPowerPrimeFiniteAlgebra (A := A) p n →ₐ[A] Q := by
  let g : MvPolynomial (Fin n) A →ₐ[A] Q :=
    (Ideal.Quotient.mkₐ A _).comp (MvPolynomial.rename (fun i : Fin n => (i : ℕ)))
  apply Ideal.Quotient.liftₐ _ g
  have hker : monicPowerFamilyRelationIdeal p (Fin n) A (fun _ => 0) ≤
      RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ p - MvPolynomial.C (0 : A)) = 0
    simp only [g, map_pow, AlgHom.comp_apply, MvPolynomial.rename_X, map_zero, sub_zero]
    change (Ideal.Quotient.mk (monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0))
      (MvPolynomial.X i.val)) ^ p = 0
    simpa only [map_zero] using monicPowerFamilyQuotient_root_pow p ℕ A (fun _ => 0) i.val
  exact fun _ hx => hker hx

/-- 概要：有限から可算への標準射は商の多項式を変数名変更で送る。
方針：商からの普遍射の評価を展開する。
規約：添字は Fin n の自然数値を使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限支持への制限。 -/
theorem dividedPowerPrimeFiniteToCountable_mk (n : ℕ) (F : MvPolynomial (Fin n) A) :
    dividedPowerPrimeFiniteToCountable (A := A) p n (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (MvPolynomial.rename (fun i : Fin n => (i : ℕ)) F) := rfl

/-- 概要：可算切断商の任意の元はある有限初期変数商から来る。
方針：代表多項式の有限変数集合の上限より大きい段を選び、名前変更で引き戻す。
規約：係数環の非零性や標数を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の可算評価の単射性を有限段へ帰着する。 -/
theorem dividedPowerPrimeCountable_exists_finite (x : Q) :
    ∃ (n : ℕ) (y : DividedPowerPrimeFiniteAlgebra (A := A) p n),
      dividedPowerPrimeFiniteToCountable p n y = x := by
  classical
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  let n := F.vars.sup id + 1
  have hvars : (F.vars : Set ℕ) ⊆ Set.range (fun i : Fin n => (i : ℕ)) := by
    intro i hi
    refine ⟨⟨i, ?_⟩, rfl⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  obtain ⟨G, hG⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range F
    (fun i : Fin n => (i : ℕ)) Fin.val_injective hvars
  refine ⟨n, Ideal.Quotient.mk _ G, ?_⟩
  rw [dividedPowerPrimeFiniteToCountable_mk, hG]

/-- 概要：有限段の評価は可算段への標準射と可算評価の合成に一致する。
方針：商と多項式の外延性で各変数の評価 γₚⁱ を比較する。
規約：p は素数で係数環内で零。
使われ方：BS Rem 7.15(1)（著者版 p.62）の単射性の移送。 -/
theorem dividedPowerPrimeTruncatedEval_comp_finite [Fact p.Prime]
    (hp : (p : A) = 0) (n : ℕ) :
    (dividedPowerPrimeTruncatedEval (A := A) p hp).comp
      (dividedPowerPrimeFiniteToCountable p n) = dividedPowerPrimeFiniteEval p n hp := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change dividedPowerPrimeTruncatedEval p hp
    (dividedPowerPrimeFiniteToCountable p n (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
  rw [dividedPowerPrimeFiniteToCountable_mk, MvPolynomial.rename_X]
  exact (dividedPowerPrimeTruncatedEval_X p hp i.val).trans
    (dividedPowerPrimeFiniteEval_X p n hp i).symm

/-- 概要：可算切断多項式商から一元分冪代数への標準評価は単射。
方針：核の任意の元を有限段から持ち上げ、有限評価の単射性で零とする。
規約：係数環の非零性や追加の平坦性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示的な自由切断表示。 -/
theorem dividedPowerPrimeTruncatedEval_injective [Fact p.Prime] (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeTruncatedEval (A := A) p hp) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨n, y, rfl⟩ := dividedPowerPrimeCountable_exists_finite p x
  have hy : dividedPowerPrimeFiniteEval p n hp y = 0 := by
    rw [← dividedPowerPrimeTruncatedEval_comp_finite]
    exact hx
  have hy0 : y = 0 := (dividedPowerPrimeFiniteEval_injective p n hp)
    (hy.trans (map_zero _).symm)
  rw [hy0, map_zero]

/-- 概要：可算切断多項式商は標準評価によって一元分冪代数に同型。
方針：有限支持から得た単射性と素数冪分冪の生成による全射性を束ねる。
規約：変数 i は γₚⁱ に対応し、原典の γ₁=f の商はまだ課さない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 表示計算の基礎同型。 -/
def dividedPowerPrimeTruncatedEquiv [Fact p.Prime] (hp : (p : A) = 0) :
    Q ≃ₐ[A] DividedPowerAlgebra A A :=
  AlgEquiv.ofBijective (dividedPowerPrimeTruncatedEval p hp)
    ⟨dividedPowerPrimeTruncatedEval_injective p hp,
      dividedPowerPrimeTruncatedEval_surjective p hp⟩


/-- 概要：切断表示の代数同型は変数 i を γₚⁱ に送る。
方針：同型の順射が標準評価であることと既存の変数公式を使う。
規約：最初の変数 i=0 は一次分冪 γ₁ に対応する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の γ₁=f の商の比較。 -/
theorem dividedPowerPrimeTruncatedEquiv_X [Fact p.Prime] (hp : (p : A) = 0) (i : ℕ) :
    dividedPowerPrimeTruncatedEquiv p hp (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      DividedPowerAlgebra.dp A (p ^ i) (1 : A) :=
  dividedPowerPrimeTruncatedEval_X p hp i

end SerrePositivity.BhattScholze.Andre
