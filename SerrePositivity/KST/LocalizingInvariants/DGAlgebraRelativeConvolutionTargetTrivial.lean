module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionFibration
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PullbackHomTargetTrivial

/-!
概要：全射擬同型な標的射に対する実相対 AW 制限は擬同型。
方針：E2 の同じ正規化 pullback-Hom の証拠を、両射影を保つ底の実同型で戻す。
規約：小さい単体集合の任意の単射を許し、元の射 q の性質を用いる。
使われ方：実境界充填と cell 写像模型の標的擬同型不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {X B : Mon (Complex R)}
  (q : X ⟶ B) {K L : SSet.{0}} (f : K ⟶ L) [Mono f]

lemma relativeConvolutionRestriction_quasiIso_of_target_trivial
    (hs : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R q.hom) (hq : QuasiIso q.hom) :
    QuasiIso (relativeConvolutionRestriction R q f).hom := by
  rw [relativeConvolutionRestriction_hom_eq]
  have := (_root_.SerrePositivity.ComplexLimits.normalizedPullbackHom_target_trivialFibration
    f q.hom hs hq).2
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
