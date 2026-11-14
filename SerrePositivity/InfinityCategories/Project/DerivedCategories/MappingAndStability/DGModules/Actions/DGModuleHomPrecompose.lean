module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! # dg 加群の閉射による Hom 成分の前合成

概要：閉射の単位由来の次数零成分による合成を前合成 chain map と同定する。
方針：全 Hom end の評価で既存の自然性の式を照合する。
規約：任意次数で成立する。使われ方：β3 の cone の微分の線形計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N X : ModuleCategory A D}

/-- 閉零射による全次数の前合成は Hom 複体の鎖写像の成分に一致する。 -/
lemma dgModuleHom_precompose_eq_compose (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) X) n) :
    (eHomWhiskerRight (Complex A) f X).f n z =
      compose A z (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add n) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π]
  have h := moduleHomWhiskerRight_apply_π A D (M := M) (N := N) (P := X) f n z x
  rw [moduleEvaluation_cochain A D x f] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
