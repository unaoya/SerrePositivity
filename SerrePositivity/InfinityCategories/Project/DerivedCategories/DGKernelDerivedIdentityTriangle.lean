module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveIsoNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedIsoAlgebra
public import SerrePositivity.DifferentialGraded.Tensor.Graded
/-!
概要：二つの対角 kernel を使う三角式と左単位の coherence を、同じ全関手同型で扱う。
方針：元の dg 三角・全関手同型の実交換則・同じ指定単位を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：元の導来 kernel の左単位三角式。
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
local notation "a" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R E E E D I I P
local notation "l" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E E
  (Iso.refl p) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E E I)
omit [Small.{u} D] in
/-- 二つの対角 kernel を含む元の dg 三角式を、同じ指定同型の等式へ戻す。 -/
lemma dgKernelBimodule_identity_triangle : a ≪≫ l = q := by
  apply Iso.ext
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso_hom, Iso.refl_hom]
  exact (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.triangle R E E D I P).symm
/-- 同じ二つの対角 kernel を含む dg 三角式の、元の導来作用の同型としての像。 -/
lemma dgKernelDerivedInfinity_identity_triangle :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E a ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E l =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E q := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso_trans, dgKernelBimodule_identity_triangle]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
