module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionLeftUnitFromPentagon
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGKernelNerveIdentityCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGKernelCompositionNerveRightUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGKernelCompositionNervePentagon
/-!
概要：元の指定合成比較と同じ左単位子の作用の三角式を証明する。
方針：同じ二重対角 kernel の三角像・自然性・五角式・右単位を使う。
規約：元の指定値を保ち、原 Hom の平坦性を追加しない。
使われ方：kernel の単位 coherence と一般 cell 模型への移送。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
local notation "I" => _root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R E
local notation "i" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E E I
local notation "p" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P
local notation "IP" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E E D I P
local notation "II" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E E E I I
/-- 元の通常合成比較と左単位子の作用は、元の通常単位の制限に一致。 -/
lemma dgKernelTensorCompositionNerveIso_left_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E E P I ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R E).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftUnitComparison_from_pentagon (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E E I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E IP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E E II))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleTensor.compose R E E D I IP)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E (BimoduleTensor.compose R E E D II P)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E E P I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R E E (BimoduleTensor.rightBimoduleUnitIso R E E I))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R E E E I I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E E IP I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E E P II)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (BimoduleTensor.associatorIso R E E E D I I P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
      (Iso.refl p) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E E I)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorNerve_identity_triangle R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorNerve_identity_first_naturality R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorNerve_identity_second_naturality R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_right_unit R E E I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_pentagon R D E E E P I I)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
