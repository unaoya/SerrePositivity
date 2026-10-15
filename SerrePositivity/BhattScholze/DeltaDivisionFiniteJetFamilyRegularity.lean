module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteJetSubset
public import Mathlib.Data.List.Nodup

/-! # 元の同段δ関係の有限族の弱正則性と実Koszul分解 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "R₀" => L₀ ⧸ I₀
local notation "f₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a s (N + 2))

/-- 元の同段δ関係の有限列のイデアルは、その添字部分集合の関係イデアル。 -/
theorem deltaDivisionFiniteJet_ofList_eq_span (l : List σ) :
    Ideal.ofList (l.map f₀) = Ideal.span (Set.range fun s : {s | s ∈ l} ↦ f₀ s) := by
  rw [Ideal.ofList]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.property, rfl⟩

include hpA hpL hg hv

/-- 元の下位関係商内の、重複しない有限同段δ関係列は弱正則。 -/
theorem deltaDivisionFiniteJet_list_isWeaklyRegular (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular R₀ (l.map f₀) := by
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
  have h := deltaDivisionFiniteJetSubset_next_isSMulRegular
    D hpA hpL hg d a v hv N {s | s ∈ l.take i} l[i] hs
  have hr : IsSMulRegular
      (R₀ ⧸ Ideal.span (Set.range fun s : {s | s ∈ l.take i} ↦ f₀ s)) (f₀ l[i]) :=
    (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp h
  have hI : (Ideal.ofList ((l.map f₀).take i) • ⊤ : Submodule R₀ R₀) =
      Ideal.span (Set.range fun s : {s | s ∈ l.take i} ↦ f₀ s) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take,
      deltaDivisionFiniteJet_ofList_eq_span]
  rw [hI, List.getElem_map]
  exact hr

/-- Fin mの単射で指定する元の同段δ関係の有限族は弱正則。 -/
theorem deltaDivisionFiniteJet_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular R₀ (List.ofFn fun i ↦ f₀ (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    deltaDivisionFiniteJet_list_isWeaklyRegular D hpA hpL hg d a v hv N
      (List.ofFn s) (List.nodup_ofFn_ofInjective hs)

/-- 元の同段δ関係の異なる有限族は、具体的下位商上の実Koszul分解を与える。 -/
theorem deltaDivisionFiniteJet_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦ f₀ (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionFiniteJet_fin_isWeaklyRegular D hpA hpL hg d a v hv N s hs)

/-- 有限添字の場合、元の全同段δ関係は具体的下位商上の実Koszul分解を与える。 -/
theorem deltaDivisionFiniteJet_all_isKoszulResolution [Fintype σ] :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin (Fintype.card σ) ↦ f₀ ((Fintype.equivFin σ).symm i)) :=
  deltaDivisionFiniteJet_fin_isKoszulResolution D hpA hpL hg d a v hv N
    (Fintype.equivFin σ).symm (Fintype.equivFin σ).symm.injective

omit hpA hpL hg hv in
/-- 有限全列挙の生成イデアルは、元の全同段δ関係の像のspan。 -/
theorem deltaDivisionFiniteJet_all_span [Fintype σ] :
    Ideal.span (Set.range fun i : Fin (Fintype.card σ) ↦ f₀ ((Fintype.equivFin σ).symm i)) =
      Ideal.span (Set.range f₀) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin σ).symm i, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨Fintype.equivFin σ s, ?_⟩
    simp only [Equiv.symm_apply_apply]

end SerrePositivity.BhattScholze
