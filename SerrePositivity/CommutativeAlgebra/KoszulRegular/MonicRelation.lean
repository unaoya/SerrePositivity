module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Defs
public import SerrePositivity.CommutativeAlgebra.Polynomial.MonicRelation
public import SerrePositivity.CommutativeAlgebra.Polynomial.IndependentMonicQuotient

public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.Data.List.Nodup

/-!
# モニック関係列の弱正則性と Koszul 分解

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実残余 Koszul 入力。 -/
theorem monicRelation_fin_isKoszulResolution (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ (fun s => monicRelation (f s) s) (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (monicRelation_fin_isWeaklyRegular f hf s hs)

/-- 概要：負のモニック関係の異なる有限族も弱正則列。
方針：モニック族の有限弱正則性に一括符号変更を適用する。
規約：正次数を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最初の実 δ 関係の弱正則性。 -/
theorem monicRelation_neg_fin_isWeaklyRegular (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic) {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i => -monicRelation (f (s i)) (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    SerrePositivity.isWeaklyRegular_map_neg _ (monicRelation_fin_isWeaklyRegular f hf s hs)

end SerrePositivity.BhattScholze.Andre

end MonicRelationRegularSequencePart
