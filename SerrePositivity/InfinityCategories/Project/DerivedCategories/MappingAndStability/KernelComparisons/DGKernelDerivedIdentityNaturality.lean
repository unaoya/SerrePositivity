module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedCompositionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedIdentityTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoWhiskerRefl
/-!
概要：二つの対角 kernel を含む三角式と、同じ単位子に関する指定比較の自然性。
方針：元の三角式・指定比較の自然性・同じ恒等同型の前後合成を使う。
規約：原 Hom の平坦性を追加しない。使われ方：元の左単位三角式の回収。
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
local notation "hII" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R E E E I I hI hI
include hP in
/-- 元の導来合成子の左単位子に関する第一変数の自然性四角形。 -/
lemma dgKernelDerivedInfinity_identity_first_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E IP I hIP ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E
      (BimoduleTensor.leftBimoduleUnitIso R E D P)).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E E I) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_naturality R D E E
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i) hIP hP hI hI
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_of_refl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R E E (Iso.refl i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso_refl R E E i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
  dsimp only [_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of] at h he
  rw [he] at h
  simpa only [Iso.refl_trans] using! h
include hP in
/-- 元の導来合成子の対角の右単位子に関する第二変数の自然性四角形。 -/
lemma dgKernelDerivedInfinity_identity_second_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P II hP ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
          (Iso.refl p) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E E I)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R E E
      (BimoduleTensor.rightBimoduleUnitIso R E E I)).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E E P I hP := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_naturality R D E E
    (Iso.refl p) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E E I) hP hP hII hI
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_of_refl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (Iso.refl p))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso_refl R D E p) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E E II)
  dsimp only [_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of] at h he
  rw [he] at h
  simpa only [Iso.refl_trans] using! h
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
