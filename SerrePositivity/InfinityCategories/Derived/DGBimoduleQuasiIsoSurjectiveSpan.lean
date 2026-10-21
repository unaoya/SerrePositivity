module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleQuasiIsoTransfer
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleQuasiIsoSpanMaps
/-!
概要：元の双加群準同型を保持する実 span の両脚は、次数別全射準同型である。
方針：同じ右加群の実 disk span の性質を評価同型と余単位で移す。
規約：元の指定射の全射性は不要。使われ方：任意の双加群準同型の実導来作用比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w)
  [DGCategory R B] [DGCategory R C] [Small.{u} B] [Small.{u} C]
/-- 同じ左脚は全評価の全整数次数で全射。 -/
lemma dgBimoduleQuasiIsoSpanLeft_degree_surjective (P Q : BimoduleCategory R B C)
    (b : B) (c : C) (n : ℤ) :
    Function.Surjective (((BimoduleCategory.valueEvaluation R B C b c).map
      (dgBimoduleQuasiIsoSpanLeft R B C P Q)).f n) := by
  apply dgBimodule_degree_surjective_postIso
  exact dgRightModuleBimodule_degree_surjective R B C _
    (dgModuleQuasiIsoSpanLeft_degree_surjective R _ _ _)
/-- 同じ右脚は、元の指定射の性質によらず全評価の全整数次数で全射。 -/
lemma dgBimoduleQuasiIsoSpanRight_degree_surjective {P Q : BimoduleCategory R B C}
    (f : P ⟶ Q) (b : B) (c : C) (n : ℤ) :
    Function.Surjective (((BimoduleCategory.valueEvaluation R B C b c).map
      (dgBimoduleQuasiIsoSpanRight R B C f)).f n) := by
  apply dgBimodule_degree_surjective_postIso
  exact dgRightModuleBimodule_degree_surjective R B C _
    (dgModuleQuasiIsoSpanRight_degree_surjective R _ _)
/-- 同じ左脚は全評価で準同型。 -/
lemma dgBimoduleQuasiIsoSpanLeft_quasiIso (P Q : BimoduleCategory R B C) :
    BimoduleCategory.quasiIso R B C (dgBimoduleQuasiIsoSpanLeft R B C P Q) := by
  apply (BimoduleCategory.quasiIso R B C).cancel_right_of_respectsIso _ _ |>.2
  exact (rightModuleBimoduleEquivalence_quasiIso_iff R B C _).2
    (dgModuleQuasiIsoSpanLeft_quasiIso R _ _ _)
/-- 元の指定射が準同型なら、同じ右脚も全評価で準同型。 -/
lemma dgBimoduleQuasiIsoSpanRight_quasiIso {P Q : BimoduleCategory R B C}
    (f : P ⟶ Q) (hf : BimoduleCategory.quasiIso R B C f) :
    BimoduleCategory.quasiIso R B C (dgBimoduleQuasiIsoSpanRight R B C f) := by
  apply (BimoduleCategory.quasiIso R B C).cancel_right_of_respectsIso _ _ |>.2
  exact (rightModuleBimoduleEquivalence_quasiIso_iff R B C _).2
    (dgModuleQuasiIsoSpanRight_quasiIso R _ _ (dgBimoduleInverse_quasiIso R B C f hf))
end SerrePositivity.InfinityCategories
