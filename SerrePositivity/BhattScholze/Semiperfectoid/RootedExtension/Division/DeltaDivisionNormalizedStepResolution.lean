module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionNormalizedStepQuotientComparison

/-! # 有限最高段Koszul複体から次段実正規化商への擬同型

有限性はこの途中の有限Koszulモデルだけに使用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "R₀" =>
  MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 実源商から次段実正規化商への具体的標準射。 -/
def deltaDivisionNormalizedStepNextMap :
    R₀ →+* DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) :=
  (deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N).toRingHom.comp
    (Ideal.Quotient.mk (deltaDivisionNormalizedStepTopIdeal D d a v N))

/-- 源商からの標準射は、元の多項式上で次段の標準商射に一致する。 -/
theorem deltaDivisionNormalizedStepNextMap_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedStepNextMap D d a v N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ f :=
  deltaDivisionNormalizedStepDoubleQuotientEquiv_mk D d a v N f

/-- 次段実商の標準実源商代数構造。 -/
@[instance_reducible] def deltaDivisionNormalizedStepNextAlgebra :
    Algebra R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)) :=
  (deltaDivisionNormalizedStepNextMap D d a v N).toAlgebra

/-- 二重商比較は標準実源商代数同型。 -/
def deltaDivisionNormalizedStepDoubleQuotientAlgEquiv :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    (R₀ ⧸ deltaDivisionNormalizedStepTopIdeal D d a v N) ≃ₐ[R₀]
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N)
  intro c
  rfl

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦
  Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (Equiv.symm (Fintype.equivFin σ) i) N)

/-- 有限全関係の実商は、次段実正規化商と標準実源商代数として同型。 -/
def deltaDivisionNormalizedStepAllQuotientAlgEquiv :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    (R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀]
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact (Ideal.quotientEquivAlgOfEq R₀ (deltaDivisionNormalizedStepAll_span D d a v N)).trans
    (deltaDivisionNormalizedStepDoubleQuotientAlgEquiv D d a v N)

/-- 最高段全関係Koszul複体の零次ホモロジーは、実際の次段正規化商。 -/
def deltaDivisionNormalizedStepHomologyZeroEquiv :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    (koszulComplex g).homology 0 ≃ₗ[R₀]
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact (deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).equiv.some.trans
    (deltaDivisionNormalizedStepAllQuotientAlgEquiv D d a v N).toLinearEquiv

/-- 有限最高段Koszul複体から次段実商の単一複体への具体的添加写像。 -/
def deltaDivisionNormalizedStepAugmentation :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    koszulComplex g ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1))) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact toSingleOfHomology _ koszulComplex_d_zero_one
    (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom

/-- 具体的な最高段Koszul添加写像は次段実正規化商への擬同型。 -/
theorem deltaDivisionNormalizedStepAugmentation_quasiIso :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    QuasiIso (deltaDivisionNormalizedStepAugmentation D d a v N) := by
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact quasiIso_toSingleOfHomology _ koszulComplex_d_zero_one
    (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom
    (deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).isZero

/-- 添加写像の零次ホモロジー射は、構成に用いた実次段商への同型に一致する。 -/
theorem deltaDivisionNormalizedStepAugmentation_homologyMap :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    HomologicalComplex.homologyMap (deltaDivisionNormalizedStepAugmentation D d a v N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)))).hom =
      (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom := by
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact toSingleOfHomology_homologyMap _ koszulComplex_d_zero_one _

/-- 有限最高段Koszul複体は、実際の次段正規化商の共通APIによる射影分解。 -/
def deltaDivisionNormalizedStepResolution :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    IsResolutionOf (koszulComplex g)
      (ModuleCat.of R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1))) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact
    { isZero_X := koszulComplex_isZero_X_of_pos g
      projective := koszulComplex_projective_X g
      isZero_homology := (deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).isZero
      homologyZeroIso := (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso }

end SerrePositivity.BhattScholze
