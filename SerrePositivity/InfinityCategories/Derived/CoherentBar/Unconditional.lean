module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarMaurerCartan
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StableHomotopyEquation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedProjection
/-!
概要：D の公開 MC 定理を代入し、元の coherent 図式の実 bar と正規化比較を無条件にする。
方針：MC 仮定付き構成を保持し、公開された元の theta の等式をそのまま渡す。
規約：追加の模型圏 instance や別の theta を導入しない。
使われ方：変形 retract と native 余錐の無条件な主経路。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarMaurerCartan_unconditional : dgCoherentBarMaurerCartan R D F :=
  dgCoherentBarTheta_maurerCartan R D F

abbrev dgCoherentBarModuleUnconditional : RightModule R D :=
  dgCoherentBarModule R D F (dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizedModuleUnconditional : RightModule R D :=
  dgCoherentBarNormalizedModule R D F (dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizedModuleProjectionUnconditional :
    ForgetEnrichment.of (Complex R) (dgCoherentBarModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) :=
  dgCoherentBarNormalizedModuleProjection R D F (dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizationEndomorphismUnconditional :
    ForgetEnrichment.of (Complex R) (dgCoherentBarModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarModuleUnconditional R D F) :=
  dgCoherentBarNormalizationEndomorphism R D F (dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizationEndomorphismHomotopyUnconditional :
    ModuleHomotopy R D (dgCoherentBarNormalizationEndomorphismUnconditional R D F) (𝟙 _) :=
  dgCoherentBarNormalizationEndomorphismHomotopy R D F
    (dgCoherentBarTheta_maurerCartan R D F)

lemma dgCoherentBarNormalizationProjectorGraded_twisted_closed_unconditional :
    dgCoherentBarTwistedEndDifferential R D F 0
      (dgCoherentBarNormalizationProjectorGraded R D F) = 0 :=
  dgCoherentBarNormalizationProjectorGraded_twisted_closed R D F
    (dgCoherentBarTheta_maurerCartan R D F)

lemma dgCoherentBarNormalizationStableHomotopyGraded_twisted_d_unconditional :
    dgCoherentBarTwistedEndDifferential R D F (-1)
      (dgCoherentBarNormalizationStableHomotopyGraded R D F) =
      dgCoherentBarNormalizationProjectorGraded R D F -
      (unitElement R
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val :=
  dgCoherentBarNormalizationStableHomotopyGraded_twisted_d R D F
    (dgCoherentBarTheta_maurerCartan R D F)

end SerrePositivity.InfinityCategories
