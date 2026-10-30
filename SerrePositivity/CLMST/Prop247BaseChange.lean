module

public import SerrePositivity.CLMST.Prop247Cone
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationCompletion
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # Prop 2.4.7：通常 tensor の完備化と標準 perfectoid 化の四角形

BS 8.13 による終域の比較は指定した B 代数同型として受け取る。
このファイルは通常 tensor と古典完備化の実標準射の図式を供給する。
完備導来底変換との同定をこの通常環の図式だけから主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (B L : Type u) [CommRing B] [CommRing L] [Algebra B L]
    [Module.FinitePresentation B L] (p : ℕ) [Fact p.Prime]

/-- 有限表示代数の古典 p 完備化への実標準射は全射。
分離性や bounded torsion をこの全射性に追加しない。 -/
theorem prop247_completion_unit_surjective (hB : IsIntegralPerfectoid B p) :
    Function.Surjective (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L)) := by
  have hL := isModuleComplete_of_finitePresentation B (p : B)
    (hB.isModuleComplete B p) (ModuleCat.of B L)
  have hL' : IsModuleComplete L (p : L) (ModuleCat.of L L) := by
    simpa only [map_natCast] using
      (isModuleComplete_algebraMap_iff B L (p : B) L).mpr hL
  let : IsPrecomplete (Ideal.span {(p : L)}) L :=
    isPrecomplete_of_adicRecurrenceMap_surjective (p : L)
      ((isModuleComplete_iff_recurrence_bijective L (p : L) _).mp hL').2
  exact AdicCompletion.of_surjective (Ideal.span {(p : L)}) L

omit [Module.FinitePresentation B L] in
/-- 原典の通常底変換 S⊗R B（係数環を左に置く）の実完備化標準射への適用。 -/
theorem prop247_tensor_completion_unit_surjective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R B] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hB : IsIntegralPerfectoid B p) :
    Function.Surjective (algebraMap (B ⊗[R] S)
      (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  exact prop247_completion_unit_surjective B (B ⊗[R] S) p hB

variable {B L} {C : Type u} [CommRing C] [Algebra B C]

omit [Module.FinitePresentation B L] in
/-- 元の B 作用を保持した、指定 perfectoid 化写像の完備化への標準延長。 -/
def prop247_completionMap (β : L →ₐ[B] C) (hβ : IsPerfectoidization p β.toRingHom) :
    AdicCompletion (Ideal.span {(p : L)}) L →ₐ[B] C :=
  { IsPerfectoidization.completionMap p hβ with
    commutes' b := by
      have h := RingHom.congr_fun (IsPerfectoidization.completionMap_comp p hβ)
        (algebraMap B L b)
      exact h.trans (β.commutes b) }

omit [Module.FinitePresentation B L] in
/-- 標準延長の単位図式は、元の全ての元について可換。 -/
theorem prop247_completionMap_unit (β : L →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom) (x : L) :
    prop247_completionMap p β hβ
      (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) x) = β x :=
  RingHom.congr_fun (IsPerfectoidization.completionMap_comp p hβ) x

omit [Module.FinitePresentation B L] in
/-- 指定された終域同型（BS 8.13 の環版の出力を受け取る位置）を含む実四角形。
右下から右上への射は e、左下から左上への射は古典完備化の標準射。 -/
theorem prop247_completion_square {T : Type u} [CommRing T] [Algebra B T]
    (β : L →ₐ[B] C) (hβ : IsPerfectoidization p β.toRingHom) (e : C ≃ₐ[B] T) :
    (e.toAlgHom.comp (prop247_completionMap p β hβ)).comp
      (IsScalarTower.toAlgHom B L (AdicCompletion (Ideal.span {(p : L)}) L)) =
      e.toAlgHom.comp β := by
  ext x
  exact congrArg e (prop247_completionMap_unit p β hβ x)

/-- 標準完備化の実図式で、β の錐零化から α の錐零化へ移す。 -/
theorem prop247_completion_cone_bound
    (hB : IsIntegralPerfectoid B p) (β : L →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom) (g : B) (q : ℕ)
    (hq : moduleMapConeScalar B β.toLinearMap (g ^ q) = 0) :
    moduleMapConeScalar B (prop247_completionMap p β hβ).toLinearMap (g ^ (2 * q)) = 0 := by
  apply moduleMapConeScalar_of_surjective_source
    (IsScalarTower.toAlgHom B L
      (AdicCompletion (Ideal.span {(p : L)}) L)).toLinearMap
    (prop247_completion_unit_surjective B L p hB)
    (prop247_completionMap p β hβ).toLinearMap β.toLinearMap _ g q hq
  ext x
  exact prop247_completionMap_unit p β hβ x

end SerrePositivity.CLMST
