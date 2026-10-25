module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteJetFamilyRegularity

/-! # 元の有限δ関係の次段実商へのKoszul擬同型と射影分解 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
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
local notation "I₁" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2)
local notation "R₀" => L₀ ⧸ I₀
local notation "R₁" => L₀ ⧸ I₁
local notation "f₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a s (N + 2))

/-- 全同段関係の商内spanは、元の関係イデアルの標準商像。 -/
theorem deltaDivisionFiniteJetStep_span_eq_map :
    Ideal.span (Set.range f₀) =
      (Ideal.span (Set.range fun s ↦ deltaDivisionIteratedRelation D d a s (N + 2))).map
        (Ideal.Quotient.mk I₀) := by
  rw [Ideal.map_span, ← Set.range_comp']

/-- 下位関係と全次段関係を合わせると、既存の次段の有限δ関係イデアルとなる。 -/
theorem deltaDivisionFiniteJetStep_sup_eq_next :
    I₀ ⊔ Ideal.span (Set.range fun s ↦ deltaDivisionIteratedRelation D d a s (N + 2)) = I₁ := by
  rw [deltaDivisionFiniteRelationIdeal_succ D d a (N + 1), ← sup_assoc]

/-- 元の下位δ関係商に全同段関係を課した二重商は、元の次段実商。 -/
def deltaDivisionFiniteJetStepQuotientEquiv : (R₀ ⧸ Ideal.span (Set.range f₀)) ≃+* R₁ :=
  (Ideal.quotEquivOfEq (deltaDivisionFiniteJetStep_span_eq_map D d a N)).trans
    ((DoubleQuot.quotQuotEquivQuotSup I₀
      (Ideal.span (Set.range fun s ↦ deltaDivisionIteratedRelation D d a s (N + 2)))).trans
      (Ideal.quotEquivOfEq (deltaDivisionFiniteJetStep_sup_eq_next D d a N)))

/-- 二重商比較は元の自由環の標準商射と両立する。 -/
theorem deltaDivisionFiniteJetStepQuotientEquiv_mk (z : L₀) :
    deltaDivisionFiniteJetStepQuotientEquiv D d a N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ z)) = Ideal.Quotient.mk _ z := by
  rw [deltaDivisionFiniteJetStepQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq (deltaDivisionFiniteJetStep_sup_eq_next D d a N))
    (DoubleQuot.quotQuotEquivQuotSup I₀
      (Ideal.span (Set.range fun s ↦ deltaDivisionIteratedRelation D d a s (N + 2)))
      (DoubleQuot.quotQuotMk I₀
        (Ideal.span (Set.range fun s ↦ deltaDivisionIteratedRelation D d a s (N + 2))) z)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 元の下位δ関係商から次段実商への標準射。 -/
def deltaDivisionFiniteJetStepMap : R₀ →+* R₁ :=
  (deltaDivisionFiniteJetStepQuotientEquiv D d a N).toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span (Set.range f₀)))

/-- 次段標準射は元の自由環の商代表をそのまま送る。 -/
theorem deltaDivisionFiniteJetStepMap_mk (z : L₀) :
    deltaDivisionFiniteJetStepMap D d a N (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ z :=
  deltaDivisionFiniteJetStepQuotientEquiv_mk D d a N z

/-- 次段実商の標準下位δ関係商代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteJetStepAlgebra : Algebra R₀ R₁ :=
  (deltaDivisionFiniteJetStepMap D d a N).toAlgebra

/-- 二重商比較は、標準下位商代数同型。 -/
def deltaDivisionFiniteJetStepQuotientAlgEquiv :
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    (R₀ ⧸ Ideal.span (Set.range f₀)) ≃ₐ[R₀] R₁ := by
  letI := deltaDivisionFiniteJetStepAlgebra D d a N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionFiniteJetStepQuotientEquiv D d a N)
  intro c
  rfl

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦ f₀ (Equiv.symm (Fintype.equivFin σ) i)

/-- 有限全同段関係の実商は、元の次段δ関係商と標準下位商代数として同型。 -/
def deltaDivisionFiniteJetStepAllQuotientAlgEquiv :
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    (R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] R₁ := by
  letI := deltaDivisionFiniteJetStepAlgebra D d a N
  exact (Ideal.quotientEquivAlgOfEq R₀ (deltaDivisionFiniteJet_all_span D d a N)).trans
    (deltaDivisionFiniteJetStepQuotientAlgEquiv D d a N)

/-- 元の全同段Koszul複体の零次ホモロジーは、元の次段実商。 -/
def deltaDivisionFiniteJetStepHomologyZeroEquiv :
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    (koszulComplex g).homology 0 ≃ₗ[R₀] R₁ := by
  letI := deltaDivisionFiniteJetStepAlgebra D d a N
  exact (deltaDivisionFiniteJet_all_isKoszulResolution D hpA hpL hg d a v hv N).equiv.some.trans
    (deltaDivisionFiniteJetStepAllQuotientAlgEquiv D d a N).toLinearEquiv

/-- 元の全同段Koszul複体から次段実商の単一複体への具体的添加写像。 -/
def deltaDivisionFiniteJetStepAugmentation :
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    koszulComplex g ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R₀ R₁) := by
  letI := deltaDivisionFiniteJetStepAlgebra D d a N
  exact toSingleOfHomology _ koszulComplex_d_zero_one
    (deltaDivisionFiniteJetStepHomologyZeroEquiv D hpA hpL hg d a v hv N).toModuleIso.hom

/-- 元の全同段Koszul添加写像は、元の次段実商への擬同型。 -/
theorem deltaDivisionFiniteJetStepAugmentation_quasiIso :
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    QuasiIso (deltaDivisionFiniteJetStepAugmentation D hpA hpL hg d a v hv N) := by
  let := deltaDivisionFiniteJetStepAlgebra D d a N
  exact quasiIso_toSingleOfHomology _ koszulComplex_d_zero_one
    (deltaDivisionFiniteJetStepHomologyZeroEquiv D hpA hpL hg d a v hv N).toModuleIso.hom
    (deltaDivisionFiniteJet_all_isKoszulResolution D hpA hpL hg d a v hv N).isZero

/-- 元の全同段Koszul複体は、元の次段実δ関係商の共通APIによる射影分解。 -/
def deltaDivisionFiniteJetStepResolution :
    letI := deltaDivisionFiniteJetStepAlgebra D d a N
    IsResolutionOf (koszulComplex g) (ModuleCat.of R₀ R₁) := by
  letI := deltaDivisionFiniteJetStepAlgebra D d a N
  exact
    { isZero_X := koszulComplex_isZero_X_of_pos g
      projective := koszulComplex_projective_X g
      isZero_homology :=
        (deltaDivisionFiniteJet_all_isKoszulResolution D hpA hpL hg d a v hv N).isZero
      homologyZeroIso :=
        (deltaDivisionFiniteJetStepHomologyZeroEquiv D hpA hpL hg d a v hv N).toModuleIso }

end SerrePositivity.BhattScholze
