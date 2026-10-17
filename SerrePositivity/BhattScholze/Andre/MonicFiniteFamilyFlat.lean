module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyOptionQuotient
public import SerrePositivity.BhattScholze.Andre.MonicFamilyQuotientReindex
public import Mathlib.Data.Fintype.Option

/-!
# André E1・E2：有限モニック族の通常商の自由性と忠実平坦性

## 概要

有限な正次数モニック多項式族に独立な根を添加した通常商は、係数環上自由かつ忠実平坦。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の有限族の通常代数部分である。

## 方針

有限添字集合を空集合・Option・再添字付けで帰納する。
一変数追加の代数同型により AdjoinRoot のモニック剰余基底を重ね、
非零係数環では正次数から各段の非零性を証明する。

## 規約

零係数環を許す。通常の商の結果であり、完備化や perfectoid 化後の忠実平坦性は含まない。
原典の Prop 7.11 の経路と異なる、明示的な通常根添加の計算である。

## 使われ方

任意族の通常商を有限部分族から組み立てる際の自由性・忠実平坦性の入力に用いる。
-/

@[expose] public noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：非零係数環上の有限な正次数モニック族の通常商は自由かつ非零。
方針：有限型の空集合・Option 帰納で自由基底と非零性を同時に保持する。
規約：各多項式に正次数を要求し、定数 1 による零商を除外する。
使われ方：BS Rem 7.15（著者版 p.62）の有限族の通常商の忠実平坦性。 -/
theorem monicFiniteFamilyQuotient_free_nontrivial
    {R : Type u} [CommRing R] [Nontrivial R] {σ : Type v} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.Free R (PolynomialFamilyQuotient f) ∧ Nontrivial (PolynomialFamilyQuotient f) := by
  let P : Type v → Prop := fun τ => ∀ (g : τ → Polynomial R),
    (∀ t, (g t).Monic) → (∀ t, 0 < (g t).natDegree) →
    Module.Free R (PolynomialFamilyQuotient g) ∧ Nontrivial (PolynomialFamilyQuotient g)
  have hall : P σ := Finite.induction_empty_option (P := P)
    (fun {α β} e ih => by
      intro g hg hd
      obtain ⟨hfree, hne⟩ := ih (fun s : α => g (e s)) (fun s => hg (e s)) (fun s => hd (e s))
      let := hfree
      let := hne
      let e' : PolynomialFamilyQuotient g ≃ₐ[R]
          PolynomialFamilyQuotient (fun s : α => g (e s)) := by
        simpa only [Equiv.symm_symm] using polynomialFamilyReindexEquiv e.symm g
      exact ⟨Module.Free.of_equiv e'.symm.toLinearEquiv, e'.toEquiv.nontrivial⟩)
    (by
      intro g _ _
      have hI : polynomialFamilyRelationIdeal g = ⊥ := by
        simp only [polynomialFamilyRelationIdeal, Set.range_eq_empty, Ideal.span_empty]
      change Module.Free R (MvPolynomial PEmpty R ⧸ polynomialFamilyRelationIdeal g) ∧
        Nontrivial (MvPolynomial PEmpty R ⧸ polynomialFamilyRelationIdeal g)
      rw [hI]
      let e := AlgEquiv.quotientBot R (MvPolynomial PEmpty R)
      exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, e.toEquiv.nontrivial⟩)
    (by
      intro α _ ih g hg hd
      let g₀ := fun s : α => g (some s)
      let Q := PolynomialFamilyQuotient g₀
      obtain ⟨hfree, hne⟩ := ih g₀ (fun s => hg (some s)) (fun s => hd (some s))
      let := hfree
      let := hne
      let h := (g none).map (algebraMap R Q)
      let B := AdjoinRoot h
      have hm : h.Monic := (hg none).map (algebraMap R Q)
      have hn : 0 < h.natDegree := by
        rw [(hg none).natDegree_map]
        exact hd none
      let : Nontrivial B := (AdjoinRoot.of.injective_of_monic_of_degree_pos hm
        (Polynomial.natDegree_pos_iff_degree_pos.mp hn)).nontrivial
      let : Module.Free Q B := hm.free_adjoinRoot
      let : Module.Free R B := Module.Free.trans (R := R) (S := Q) (M := B)
      let e := polynomialFamilyOptionEquiv g
      exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, e.toEquiv.nontrivial⟩) σ
  exact hall f hf hdeg

/-- 概要：任意可換環上の有限正次数モニック族の通常商は自由かつ忠実平坦。
方針：非零係数環では前定理の自由性と非零性を使い、零係数環は加群の自明性で処理する。
規約：標準商の元の係数作用を保つ。
使われ方：BS Thm 7.14（著者版 p.61）の通常の有限同時根添加。 -/
theorem monicFiniteFamilyQuotient_free_faithfullyFlat
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.Free R (PolynomialFamilyQuotient f) ∧
      Module.FaithfullyFlat R (PolynomialFamilyQuotient f) := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    let : Subsingleton (PolynomialFamilyQuotient f) := Module.subsingleton R _
    refine ⟨inferInstance, ?_⟩
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    obtain ⟨hfree, hne⟩ := monicFiniteFamilyQuotient_free_nontrivial f hf hdeg
    let := hfree
    let := hne
    exact ⟨inferInstance, inferInstance⟩

/-- 概要：有限正次数モニック族の根を同時に持つ自由忠実平坦な通常拡大が存在する。
方針：標準の根族商とその係数射・変数像を取る。
規約：R と添字を同じ宇宙に置き、拡大も同じ宇宙に取る。perfectoid 性は結論しない。
使われ方：BS Thm 7.14（著者版 p.61）の通常同時根添加の有限段。 -/
theorem exists_finiteMonicRootedFaithfullyFlat
    {R : Type u} [CommRing R] {σ : Type u} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      (letI := φ.toAlgebra; Module.Free R T ∧ Module.FaithfullyFlat R T) ∧
        ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  refine ⟨PolynomialFamilyQuotient f, inferInstance, algebraMap R _,
    polynomialFamilyQuotientRoot f, ?_, polynomialFamilyQuotient_eval f⟩
  rw [toAlgebra_algebraMap]
  exact monicFiniteFamilyQuotient_free_faithfullyFlat f hf hdeg

end SerrePositivity.BhattScholze.Andre
