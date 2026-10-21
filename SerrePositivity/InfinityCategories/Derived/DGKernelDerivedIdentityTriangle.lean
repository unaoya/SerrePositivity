module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveIsoNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedIsoAlgebra
public import SerrePositivity.DifferentialGraded.Tensor.Triangle
/-!
概要：二つの対角 kernel を使う三角式と左単位の coherence を、同じ全関手同型で扱う。
方針：元の dg 三角・全関手同型の実交換則・同じ指定単位を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：元の導来 kernel の左単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D)
local notation "I" => Bimodule.diagonal R E
local notation "i" => BimoduleCategory.of R E E I
local notation "p" => BimoduleCategory.of R E D P
local notation "a" => BimoduleTensor.associatorIso R E E E D I I P
local notation "l" => dgKernelBimoduleComposeIso R D E E
  (BimoduleTensor.leftBimoduleUnitIso R E D P) (Iso.refl i)
local notation "q" => dgKernelBimoduleComposeIso R D E E
  (Iso.refl p) (BimoduleTensor.rightBimoduleUnitIso R E E I)
omit [Small.{u} D] in
/-- 二つの対角 kernel を含む元の dg 三角式を、同じ指定同型の等式へ戻す。 -/
lemma dgKernelBimodule_identity_triangle : a ≪≫ l = q := by
  apply Iso.ext
  simp only [Iso.trans_hom, dgKernelBimoduleComposeIso_hom, Iso.refl_hom]
  exact (BimoduleTensor.triangle R E E D I P).symm
/-- 同じ二つの対角 kernel を含む dg 三角式の、元の導来作用の同型としての像。 -/
lemma dgKernelDerivedInfinity_identity_triangle :
    dgKernelDerivedInfinity_bimoduleIso R D E a ≪≫
      dgKernelDerivedInfinity_bimoduleIso R D E l =
    dgKernelDerivedInfinity_bimoduleIso R D E q := by
  rw [← dgKernelDerivedInfinity_bimoduleIso_trans, dgKernelBimodule_identity_triangle]
end
end SerrePositivity.InfinityCategories
