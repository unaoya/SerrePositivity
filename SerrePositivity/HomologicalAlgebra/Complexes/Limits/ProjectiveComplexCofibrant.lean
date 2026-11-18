module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectiveCokernelCofibration

/-!
# 射影 K-projective 複体と上に有界な cokernel

概要：各次数射影の K-projective 複体は実射影 cofibrant。
方針：零射の cokernel 同型を使い、一般の全障害消滅判定へ渡す。
規約：上に有界な場合だけを K-projective 性の代用品として使わない。
使われ方：正規化単体・境界と非有界テンソル模型の cofibrancy。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma projectiveCofibrant_of_isKProjective (P : Complex A)
    [∀ n : ℤ, Projective (P.X n)] [P.IsKProjective] :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P) := by
  let i : (HomologicalComplex.zero : Complex A) ⟶ P := 0
  let e : cokernel i ≅ P := cokernelZeroIsoTarget
  have : Mono i := HomologicalComplex.isZero_zero.mono i
  have (n : ℤ) : Projective ((cokernel i).X n) :=
    Projective.of_iso ((HomologicalComplex.eval _ _ n).mapIso e.symm)
      (inferInstanceAs (Projective (P.X n)))
  have : CochainComplex.IsKProjective (cokernel i) := isKProjective_of_iso e.symm
  exact _root_.SerrePositivity.ComplexLimits.projectiveCofibration_of_projectiveCokernel i

lemma projectiveCofibrant_of_boundedAbove (P : Complex A) (d : ℤ)
    [P.IsStrictlyLE d] [∀ n : ℤ, Projective (P.X n)] :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P) := by
  have : P.IsKProjective := isKProjective_of_projective P d
  exact _root_.SerrePositivity.ComplexLimits.projectiveCofibrant_of_isKProjective P

lemma projectiveCofibration_of_boundedAboveCokernel {W Z : Complex A} (i : W ⟶ Z)
    [Mono i] (d : ℤ) [Z.IsStrictlyLE d] [∀ n : ℤ, Projective ((cokernel i).X n)] :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp i := by
  have : (cokernel i).IsStrictlyLE d := by
    rw [isStrictlyLE_iff]
    intro n hn
    exact IsZero.of_epi ((cokernel.π i).f n) (Z.isZero_of_isStrictlyLE d n hn)
  have : CochainComplex.IsKProjective (cokernel i) := isKProjective_of_projective (cokernel i) d
  exact _root_.SerrePositivity.ComplexLimits.projectiveCofibration_of_projectiveCokernel i

end SerrePositivity.ComplexLimits
