module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTransition
public import SerrePositivity.KST.LocalizingInvariants.CochainSeparatedBounds

/-!
概要：隣接 Postnikov 切断の下端の cycles 層と、その元の代数への包含を構成する。
方針：τ≥−(n+1) の smart τ≤−(n+1) を取り、次数の上下界で零性を示す。
規約：この層を厳密な kernel と同一視しない。使われ方：導来平方零層との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

instance postnikov_lowerBound : (postnikov R B n).X.IsStrictlyGE (-n) :=
  postnikovComplex_lowerBound R B n

def postnikovLayer : Complex R := (postnikov R B (n + 1)).X.truncLE (-(n + 1))

def postnikovLayerInclusion : postnikovLayer R B n ⟶ (postnikov R B (n + 1)).X :=
  (postnikov R B (n + 1)).X.ιTruncLE (-(n + 1))

instance postnikovLayer_upperBound : (postnikovLayer R B n).IsStrictlyLE (-(n + 1)) := by
  change (HomologicalComplex.truncLE _ (embeddingUpIntLE (-(n + 1)))).IsStrictlySupported _
  infer_instance

instance postnikovLayerInclusion_mono : Mono (postnikovLayerInclusion R B n) := by
  change Mono (HomologicalComplex.ιTruncLE _ (embeddingUpIntLE (-(n + 1))))
  infer_instance

instance postnikovLayer_lowerBound : (postnikovLayer R B n).IsStrictlyGE (-(n + 1)) := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  have : Mono ((postnikovLayerInclusion R B n).f i) := by
    change Mono ((HomologicalComplex.ιTruncLE _ (embeddingUpIntLE (-(n + 1)))).f i)
    infer_instance
  exact IsZero.of_mono ((postnikovLayerInclusion R B n).f i)
    (((postnikovComplex R (n + 1)).obj B).isZero_of_isStrictlyGE (-(n + 1)) i hi)

lemma postnikovLayerInclusion_transition_zero :
    postnikovLayerInclusion R B n ≫ (postnikovTransition R B (n + 1) n (by omega)).hom = 0 :=
  cochainHom_eq_zero_of_bounds (-(n + 1)) (-n) (by omega) _

lemma postnikovLayer_mul_zero (hn : 0 ≤ n) :
    (postnikovLayerInclusion R B n ⊗ₘ postnikovLayerInclusion R B n) ≫
      μ[(postnikov R B (n + 1)).X] = 0 :=
  cochainBilinear_eq_zero_of_bounds (-(n + 1)) (-(n + 1)) (-(n + 1)) (by omega) _

lemma postnikovLayer_exists_iso_single : ∃ M : ModuleCat R,
    Nonempty (postnikovLayer R B n ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) (-(n + 1))).obj M) :=
  CochainComplex.exists_iso_single _ (-(n + 1))

lemma postnikovLayerInclusion_quasiIsoAt :
    QuasiIsoAt (postnikovLayerInclusion R B n) (-(n + 1)) :=
  CochainComplex.quasiIsoAt_ιTruncLE _ _ _ le_rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
