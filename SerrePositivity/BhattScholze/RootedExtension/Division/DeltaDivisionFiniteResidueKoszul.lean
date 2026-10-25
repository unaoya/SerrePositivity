module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFirstJetResidueRegular
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteJetRegularity

/-! # 一元一般除算の全有限δ列のmod(p,d)Koszul分解

初項の正則性と既存の初期・高段の正則性を合成する。
通常のmod(p,d)商上の計算であり、実導来完備化後の平坦性は結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "B₀" => Ideal.span {(p : L₀), MvPolynomial.C d}
local notation "R₀" => L₀ ⧸ B₀
local notation "q₀" => Ideal.Quotient.mk B₀
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- mod(p,d)で有限δ関係を課す二重商と、元の自由環の実有限剰余商との標準比較。 -/
def deltaDivisionFiniteResidueQuotientEquiv (N : ℕ) :
    (R₀ ⧸ (I₀ N).map q₀) ≃+* (L₀ ⧸ (B₀ ⊔ I₀ N)) :=
  DoubleQuot.quotQuotEquivQuotSup B₀ (I₀ N)

/-- 二重商比較は元の自由環の標準像を保つ。 -/
theorem deltaDivisionFiniteResidueQuotientEquiv_mk (N : ℕ) (f : L₀) :
    deltaDivisionFiniteResidueQuotientEquiv D d a N
      (Ideal.Quotient.mk ((I₀ N).map q₀) (q₀ f)) = Ideal.Quotient.mk (B₀ ⊔ I₀ N) f :=
  DoubleQuot.quotQuotEquivQuotSup_quotQuotMk B₀ (I₀ N) f

variable [Unique σ]
local notation "g₀" => deltaDivisionIteratedRelation D d a (default : σ)

/-- 一元有限δ列の実mod(p,d)像の生成イデアルは、既存の有限関係イデアルの像。 -/
theorem deltaDivisionFiniteResidueRelations_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) = (I₀ N).map q₀ := by
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

/-- 初期と高段の正規化を合成し、実mod(p,d)有限前段商上の次δ関係の正則性を得る。 -/
theorem deltaDivisionFiniteResidueNext_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    IsSMulRegular (R₀ ⧸ (I₀ N).map q₀)
      (Ideal.Quotient.mk ((I₀ N).map q₀) (q₀ (g₀ (N + 1)))) := by
  have hr : IsSMulRegular (L₀ ⧸ (B₀ ⊔ I₀ N))
      (Ideal.Quotient.mk (B₀ ⊔ I₀ N) (g₀ (N + 1))) := by
    cases N with
    | zero => exact deltaDivisionFirstJet_residue_isSMulRegular D d a v hv default
    | succ n =>
        exact deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hg d a v hv n default
  let e := deltaDivisionFiniteResidueQuotientEquiv D d a N
  have he : e (Ideal.Quotient.mk ((I₀ N).map q₀) (q₀ (g₀ (N + 1)))) =
      Ideal.Quotient.mk (B₀ ⊔ I₀ N) (g₀ (N + 1)) :=
    deltaDivisionFiniteResidueQuotientEquiv_mk D d a N _
  intro x y hxy
  apply e.injective
  apply hr
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 初項が正則なら、一般dの実mod(p,d)反復δ列の全有限prefixは弱正則。 -/
theorem deltaDivisionFiniteResidueRelations_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : IsSMulRegular R₀ (q₀ (g₀ 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀
      (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) := by
  induction N with
  | zero =>
      rw [List.ofFn_succ, List.ofFn_zero,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      exact h0
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) • ⊤ :
          Submodule R₀ R₀) = (I₀ N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaDivisionFiniteResidueRelations_ofList]
      change IsSMulRegular (R₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) • ⊤ : Submodule R₀ R₀))
        (q₀ (g₀ (N + 1)))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk ((I₀ N).map q₀)) (fun _ => rfl)).mp
        (deltaDivisionFiniteResidueNext_isSMulRegular D d a hpA hpL hg v hv N)

/-- 全有限δ深さの実mod(p,d)Koszul複体は、対応する実通常商を分解する。 -/
theorem deltaDivisionFiniteResidueRelations_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : IsSMulRegular R₀ (q₀ (g₀ 0))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => q₀ (g₀ i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionFiniteResidueRelations_isWeaklyRegular D d a hpA hpL hg v hv h0 N)

end SerrePositivity.BhattScholze
