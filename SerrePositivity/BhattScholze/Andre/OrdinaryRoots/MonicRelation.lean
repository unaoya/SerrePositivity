module

public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Family
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.Data.List.Nodup

/-! # 独立なモニック関係の有限弱正則列（André E1・E2）

## 概要

独立な変数ごとのモニック関係は、重複しない有限な添字の列で弱正則列をなし、Koszul 分解を与える（`monicRelation_fin_isWeaklyRegular`・`monicRelation_fin_isKoszulResolution`）。BS Rem 7.15（著者版 p.62）の一般の f/d 包の残りの計算の入力。

## 方針

先行する添字の集合による商を使い、後続のモニック関係が各位置で非零因子であることを適用する。原典の Prop 7.11 とは違う、明示的な商による計算。

## 規約

正の次数も係数環の非零性も要らず、弱正則性だけを述べる。旧 `CommutativeAlgebra/MonicRelationRegularSequence`（`OrdinaryRoots/Family` の多項式の補題を使うので 2a で BS の下へ移した。それらを CommutativeAlgebra へ下ろせば共有層に戻せる）。

## 使われ方

(p, d) 商の最初の δ 関係と全有限 δ 深さの Koszul 分解（BS Andre）、KST/DerivedBlowup/UniversalRegularSequence。
-/

@[expose] public noncomputable section

universe u v w

section MonicRelationRegularSequencePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {σ : Type v}

/-- 概要：有限モニック関係列の生成イデアルは、その添字集合のモニック関係イデアル。
方針：先行添字の関係商で残りのモニック関係の正則性を用いる。
規約：係数環の非零性や多項式の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
theorem monicRelation_ofList_eq_subset (f : σ → Polynomial A) (l : List σ) :
    Ideal.ofList (l.map (fun s => monicRelation (f s) s)) =
      polynomialSubsetRelationIdeal {s | s ∈ l} f := by
  rw [Ideal.ofList, polynomialSubsetRelationIdeal]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.property, rfl⟩

/-- 概要：異なる有限個のモニック関係は、任意係数環上の弱正則列。
方針：先行添字の関係商で残りのモニック関係の正則性を用いる。
規約：係数環の非零性や多項式の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
theorem monicRelation_list_isWeaklyRegular (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic) (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (l.map (fun s => monicRelation (f s) s)) := by
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hs : l[i] ∉ l.take i := by
    intro hm
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_take] at hji
    have he := hl.getElem_inj_iff.mp hji
    have hj' : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
    omega
  have h := polynomialSubsetQuotient_remaining_isSMulRegular
    {s | s ∈ l.take i} f (f l[i]) (hf l[i]) l[i] hs
  have hr : IsSMulRegular
      (MvPolynomial σ A ⧸ polynomialSubsetRelationIdeal {s | s ∈ l.take i} f)
      ((fun s => monicRelation (f s) s) l[i]) :=
    (isSMulRegular_map (Ideal.Quotient.mk _ ) (fun _ ↦ rfl)).mp h
  have hI : (Ideal.ofList ((l.map (fun s => monicRelation (f s) s)).take i) • ⊤ :
      Submodule (MvPolynomial σ A) (MvPolynomial σ A)) =
      polynomialSubsetRelationIdeal {s | s ∈ l.take i} f := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take,
      monicRelation_ofList_eq_subset]
  rw [hI, List.getElem_map]
  exact hr

/-- 概要：Fin nで指定した異なるモニック関係の有限族は弱正則列。
方針：先行添字の関係商で残りのモニック関係の正則性を用いる。
規約：係数環の非零性や多項式の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
theorem monicRelation_fin_isWeaklyRegular (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i ↦ (fun s => monicRelation (f s) s) (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    monicRelation_list_isWeaklyRegular f hf (List.ofFn s)
      (List.nodup_ofFn_ofInjective hs)

/-- 概要：異なる有限個のモニック関係のKoszul複体は、実際の通常商の分解。
方針：先行添字の関係商で残りのモニック関係の正則性を用いる。
規約：係数環の非零性や多項式の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
theorem monicRelation_fin_isKoszulResolution (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ (fun s => monicRelation (f s) s) (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (monicRelation_fin_isWeaklyRegular f hf s hs)

/-- 概要：負のモニック関係の異なる有限族も弱正則列。
方針：モニック族の有限弱正則性に一括符号変更を適用する。
規約：正次数を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の最初の実 δ 関係の弱正則性。 -/
theorem monicRelation_neg_fin_isWeaklyRegular (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic) {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i => -monicRelation (f (s i)) (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    SerrePositivity.isWeaklyRegular_map_neg _ (monicRelation_fin_isWeaklyRegular f hf s hs)

end SerrePositivity.BhattScholze.Andre

end MonicRelationRegularSequencePart
