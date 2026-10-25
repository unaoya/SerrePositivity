module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteEvaluationRegular

/-! # 通常環射後の有限δ列から実評価列へのKoszul分解の移送

対象環にδ構造を要求せず、各有限prefixの通常イデアルの一致を使う。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable {T : Type v} [CommRing T] (q : RelativeFreeDeltaRing (R := A) σ →+* T)
local notation "g₀" => deltaDivisionIteratedRelation D d a (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D d a (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- 通常射後の一元有限反復δ列の生成イデアルは、実有限関係イデアルの像。 -/
theorem deltaDivisionMappedIterated_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val)) = (I₀ N).map q := by
  unfold deltaDivisionFiniteRelationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- 通常射後の一元有限評価列も、同じ実有限関係イデアルの像を生成する。 -/
theorem deltaDivisionMappedEvaluation_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) = (I₀ N).map q := by
  rw [← deltaDivisionFiniteEvaluation_ofList D d a N, Ideal.map_ofList, List.map_ofFn,
    Function.comp_def]

/-- 全有限反復δ列が通常射後に弱正則なら、全有限実評価列も同じ環で弱正則。 -/
theorem deltaDivisionMappedEvaluation_isWeaklyRegular
    (hg : ∀ N : ℕ, RingTheory.Sequence.IsWeaklyRegular T
      (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular T
      (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) := by
  induction N with
  | zero =>
      simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, deltaDivisionIteratedRelation,
        deltaDivisionEvaluationRelation, Function.iterate_zero_apply] using hg 0
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hr := hg (N + 1)
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff] at hr
      have hrg := hr.2
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hrg
      have hIg : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val)) • ⊤ :
          Submodule T T) = (I₀ N).map q := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaDivisionMappedIterated_ofList]
      have hIh : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) • ⊤ :
          Submodule T T) = (I₀ N).map q := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaDivisionMappedEvaluation_ofList]
      change IsSMulRegular (T ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val)) • ⊤ : Submodule T T))
        (q (g₀ (N + 1))) at hrg
      rw [hIg] at hrg
      change IsSMulRegular (T ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) • ⊤ : Submodule T T))
        (q (h₀ (N + 1)))
      rw [hIh]
      let qN := Ideal.Quotient.mk ((I₀ N).map q)
      have hkill : I₀ N ≤ RingHom.ker (qN.comp q) := by
        intro r hr
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q hr)
      have hrg' : IsSMulRegular (T ⧸ (I₀ N).map q) ((qN.comp q) (g₀ (N + 1))) :=
        (isSMulRegular_map qN (fun _ => rfl)).mpr hrg
      exact (isSMulRegular_map qN (fun _ => rfl)).mp
        (deltaDivisionFiniteEvaluation_next_isSMulRegular_map D d a (qN.comp q) N hkill hrg')

/-- 通常環射後の全有限実評価Koszul複体は、全有限反復δ列の弱正則性から実分解となる。 -/
theorem deltaDivisionMappedEvaluation_isKoszulResolution
    (hg : ∀ N : ℕ, RingTheory.Sequence.IsWeaklyRegular T
      (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => q (h₀ i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionMappedEvaluation_isWeaklyRegular D d a q hg N)

end SerrePositivity.BhattScholze
