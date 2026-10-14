module

public import SerrePositivity.BhattScholze.DeltaRootSubsetQuotient
public import Mathlib.Data.List.Nodup

/-! # 有限根関係列の弱正則性と実Koszul分解

重複のない添字列を用いる。係数環のp正則性やNoether性は不要。
相対完全正則性・完備化後の完全平坦性は別工程。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {σ : Type v}

/-- 有限根関係列の生成イデアルは、その添字集合の根関係イデアル。 -/
theorem deltaRootRelation_ofList_eq_subset (b : σ → A) (l : List σ) :
    Ideal.ofList (l.map (deltaRootRelationFamily (p := p) b)) =
      deltaRootSubsetRelationIdeal (p := p) {s | s ∈ l} b := by
  rw [Ideal.ofList, deltaRootSubsetRelationIdeal]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.property, rfl⟩

/-- 異なる有限個の根関係は、任意係数環上の弱正則列。 -/
theorem deltaRootRelation_list_isWeaklyRegular [Fact p.Prime]
    (b : σ → A) (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (l.map (deltaRootRelationFamily (p := p) b)) := by
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
  have h := deltaRootSubsetQuotient_remaining_isSMulRegular (p := p)
    {s | s ∈ l.take i} b l[i] hs
  have hr : IsSMulRegular
      (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) {s | s ∈ l.take i} b)
      (deltaRootRelationFamily (p := p) b l[i]) :=
    (isSMulRegular_map (Ideal.Quotient.mk _ ) (fun _ ↦ rfl)).mp h
  have hI : (Ideal.ofList ((l.map (deltaRootRelationFamily (p := p) b)).take i) • ⊤ :
      Submodule (MvPolynomial σ A) (MvPolynomial σ A)) =
      deltaRootSubsetRelationIdeal (p := p) {s | s ∈ l.take i} b := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take,
      deltaRootRelation_ofList_eq_subset]
  rw [hI, List.getElem_map]
  exact hr

/-- Fin nで指定した異なる根関係の有限族は弱正則列。 -/
theorem deltaRootRelation_fin_isWeaklyRegular [Fact p.Prime]
    (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i ↦ deltaRootRelationFamily (p := p) b (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    deltaRootRelation_list_isWeaklyRegular (p := p) b (List.ofFn s)
      (List.nodup_ofFn_ofInjective hs)

/-- 異なる有限個の根関係のKoszul複体は、実際の通常商の分解。 -/
theorem deltaRootRelation_fin_isKoszulResolution [Fact p.Prime]
    (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ deltaRootRelationFamily (p := p) b (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootRelation_fin_isWeaklyRegular b s hs)

/-- 任意の係数変更後も、異なる有限根関係の標準像は実Koszul分解を与える。 -/
theorem deltaRootRelation_map_fin_isKoszulResolution [Fact p.Prime]
    {B : Type w} [CommRing B] (f : A →+* B) (b : σ → A)
    {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ MvPolynomial.map f (deltaRootRelationFamily (p := p) b (s i))) := by
  simpa only [deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X,
    MvPolynomial.map_C] using
    deltaRootRelation_fin_isKoszulResolution (p := p) (fun t ↦ f (b t)) s hs

end SerrePositivity.BhattScholze
