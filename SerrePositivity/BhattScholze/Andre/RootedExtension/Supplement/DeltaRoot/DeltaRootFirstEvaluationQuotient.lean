module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootFirstEvaluationKoszul
public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyPresentation

/-! # 一般d根添加の深さ0通常商のモニック表示

自由δ座標を係数へ移して全深さ0関係の商を表示する。
この通常商をrawδ包全体やその完備化と同一視しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "B₀" => MvPolynomial (σ × ℕ) A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b

/-- 変数交換後の実根関係の係数。 -/
def deltaRootFirstEvaluationCoefficients : σ → B₀ :=
  fun s => MvPolynomial.C d * MvPolynomial.X (s, 0) + MvPolynomial.C (b s)

/-- 自由δ環に全深さ0の実評価関係だけを課す通常イデアル。 -/
def deltaRootFirstEvaluationIdeal : Ideal L₀ :=
  Ideal.span (Set.range fun s => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ s 0)

/-- 全深さ0関係の通常商。正のδ深さの関係は課していない。 -/
abbrev DeltaRootFirstEvaluationQuotient := L₀ ⧸ deltaRootFirstEvaluationIdeal D d b

/-- 深さ0の通常イデアルは、既存の実反復δ関係の有限段0に一致する。 -/
theorem deltaRootFirstEvaluationIdeal_eq_finiteRelationIdeal :
    deltaRootFirstEvaluationIdeal D d b =
      deltaDivisionFiniteRelationIdeal E₀ (MvPolynomial.C d) c₀ 0 := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(s, 0), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hi : i.val = 0 := by omega
    exact ⟨s, by simp only [hi]⟩

/-- 変数交換による実深さ0イデアルの像はモニック根関係イデアル。 -/
theorem deltaRootFirstEvaluationIdeal_swap :
    (deltaRootFirstEvaluationIdeal D d b).map
      (MvPolynomial.commAlgEquiv A (σ × ℕ) σ).toRingHom =
      monicPowerFamilyRelationIdeal p σ B₀ (deltaRootFirstEvaluationCoefficients d b) := by
  rw [deltaRootFirstEvaluationIdeal, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun s => MvPolynomial.commAlgEquiv A (σ × ℕ) σ
    (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ s 0)) = _
  simp_rw [deltaRootFirstEvaluation_swap]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact (monicPowerFamilyRelationIdeal p σ B₀
      (deltaRootFirstEvaluationCoefficients d b)).neg_mem
        (Ideal.subset_span (Set.mem_range_self s))
  · apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    apply neg_mem_iff.mp
    exact Ideal.subset_span (Set.mem_range_self s)

/-- 深さ0通常商の、既存のモニック根添加環との標準環同型。 -/
def deltaRootFirstEvaluationQuotientEquiv :
    DeltaRootFirstEvaluationQuotient D d b ≃+*
      MonicPowerFamilyCover p σ B₀ (deltaRootFirstEvaluationCoefficients d b) :=
  (Ideal.quotientEquiv _ _ (MvPolynomial.commAlgEquiv A (σ × ℕ) σ).toRingEquiv
    (deltaRootFirstEvaluationIdeal_swap D d b).symm).trans
      (monicPowerFamilyPresentationEquiv p σ B₀ (deltaRootFirstEvaluationCoefficients d b))

/-- 自由δ座標を係数として扱う、深さ0通常商への具体的な射。 -/
def deltaRootFirstEvaluationCoefficientMap : B₀ →+* DeltaRootFirstEvaluationQuotient D d b :=
  (Ideal.Quotient.mk (deltaRootFirstEvaluationIdeal D d b)).comp (MvPolynomial.map MvPolynomial.C)

/-- 標準同型は自由δ座標係数の標準射と両立する。 -/
theorem deltaRootFirstEvaluationQuotientEquiv_coefficient (z : B₀) :
    deltaRootFirstEvaluationQuotientEquiv D d b
      (deltaRootFirstEvaluationCoefficientMap D d b z) =
      algebraMap B₀
        (MonicPowerFamilyCover p σ B₀ (deltaRootFirstEvaluationCoefficients d b)) z := by
  rw [deltaRootFirstEvaluationQuotientEquiv, RingEquiv.trans_apply]
  change monicPowerFamilyPresentationEquiv p σ B₀ (deltaRootFirstEvaluationCoefficients d b)
    (Ideal.Quotient.mk _ (MvPolynomial.commAlgEquiv A (σ × ℕ) σ
      (MvPolynomial.map MvPolynomial.C z))) = _
  have he : MvPolynomial.commAlgEquiv A (σ × ℕ) σ (MvPolynomial.map MvPolynomial.C z) =
      MvPolynomial.C z := by
    induction z using MvPolynomial.induction_on with
    | C a => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | mul_X x s hx => simp only [map_mul, MvPolynomial.map_X,
        MvPolynomial.commAlgEquiv_X, hx]
  rw [he]
  exact monicPowerFamilyPresentationEquiv_coeff p σ B₀ (deltaRootFirstEvaluationCoefficients d b) z

/-- 具体的係数射が定めるB代数構造。 -/
@[instance_reducible] def deltaRootFirstEvaluationCoefficientAlgebra :
    Algebra B₀ (DeltaRootFirstEvaluationQuotient D d b) :=
  (deltaRootFirstEvaluationCoefficientMap D d b).toAlgebra

/-- 実深さ0商の標準比較は、具体的な係数作用を保つ。 -/
def deltaRootFirstEvaluationQuotientAlgEquiv :
    letI := deltaRootFirstEvaluationCoefficientAlgebra D d b
    DeltaRootFirstEvaluationQuotient D d b ≃ₐ[B₀]
      MonicPowerFamilyCover p σ B₀ (deltaRootFirstEvaluationCoefficients d b) := by
  letI := deltaRootFirstEvaluationCoefficientAlgebra D d b
  exact AlgEquiv.ofRingEquiv (deltaRootFirstEvaluationQuotientEquiv_coefficient D d b)

/-- 一般dの全深さ0通常商は、自由δ座標の係数環上で忠実平坦。 -/
theorem deltaRootFirstEvaluationQuotient_moduleFaithfullyFlat :
    letI := deltaRootFirstEvaluationCoefficientAlgebra D d b
    Module.FaithfullyFlat B₀ (DeltaRootFirstEvaluationQuotient D d b) := by
  let := deltaRootFirstEvaluationCoefficientAlgebra D d b
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all p σ B₀
    (deltaRootFirstEvaluationCoefficients d b) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv B₀ _
    (deltaRootFirstEvaluationQuotientAlgEquiv D d b).toLinearEquiv

/-- 深さ0通常商の元のA作用と、具体的な自由δ座標係数の作用は標準の塔をなす。 -/
theorem deltaRootFirstEvaluationCoefficient_isScalarTower :
    letI := deltaRootFirstEvaluationCoefficientAlgebra D d b
    IsScalarTower A B₀ (DeltaRootFirstEvaluationQuotient D d b) := by
  let := deltaRootFirstEvaluationCoefficientAlgebra D d b
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.C x)) =
    Ideal.Quotient.mk _ (MvPolynomial.map MvPolynomial.C (MvPolynomial.C x))
  rw [MvPolynomial.map_C]

/-- 深さ0通常商は元のA係数作用についても忠実平坦。一般d・任意添字・零環を含む。 -/
theorem deltaRootFirstEvaluationQuotient_base_moduleFaithfullyFlat :
    Module.FaithfullyFlat A (DeltaRootFirstEvaluationQuotient D d b) := by
  let := deltaRootFirstEvaluationCoefficientAlgebra D d b
  have := deltaRootFirstEvaluationCoefficient_isScalarTower D d b
  let := deltaRootFirstEvaluationQuotient_moduleFaithfullyFlat D d b
  let : Module.FaithfullyFlat A B₀ := Module.FaithfullyFlat.of_linearEquiv A
    (((σ × ℕ) →₀ ℕ) →₀ A) (MvPolynomial.basisMonomials (σ × ℕ) A).repr
  exact Module.FaithfullyFlat.trans A B₀ (DeltaRootFirstEvaluationQuotient D d b)

end SerrePositivity.BhattScholze
