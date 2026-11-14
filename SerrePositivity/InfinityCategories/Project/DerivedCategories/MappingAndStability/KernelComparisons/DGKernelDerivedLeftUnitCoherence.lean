module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionLeftUnitFromPentagon
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedIdentityNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedRightUnitCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedPentagonCoherence
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
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
local notation "I" => _root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R E
local notation "i" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E E I
local notation "p" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P
local notation "IP" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E E D I P
local notation "II" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E E E I I
local notation "hI" => _root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R E
local notation "hIP" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R E E D I P hI hP
include hP in
/-- 元の指定導来合成子と左単位子の作用は、元の指定導来単位の制限に一致。 -/
lemma dgKernelDerivedInfinity_compIso_left_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R E).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftUnitComparison_from_pentagon (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E E I) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E IP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E E II)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleTensor.compose R E E D I IP))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleTensor.compose R E E D II P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (BimoduleTensor.leftBimoduleUnitIso R E D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R E E (BimoduleTensor.rightBimoduleUnitIso R E E I))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R E E E I I hI)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E IP I hIP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P II hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R E E E D I I P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
      (Iso.refl p) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E E I)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identity_triangle R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identity_first_naturality R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identity_second_naturality R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_right_unit R E E I hI)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_pentagon R D E E E P I I hP hI hI)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
