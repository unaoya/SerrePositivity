module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison


/-! # cone を標的とする全 Hom end の外延性

概要：第一・第二射影の合成が一致する斉次射は一致する。
方針：各評価で mapping cone への cochain の外延性を使う。
規約：全ての整数次数。使われ方：β3 の双対比較の原始元の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {T M N : ModuleCategory A D}

/-- 全 Hom end の cone を標的とする射は二射影により一意に決まる。 -/
lemma dgModuleConeTargetHom_ext (f : M ⟶ N) (n : ℤ)
    {z w : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) n}
    (hfst : compose A (moduleConeFstElement A D f) z rfl =
      compose A (moduleConeFstElement A D f) w rfl)
    (hsnd : compose A (moduleConeSndElement A D f) z (add_zero n) =
      compose A (moduleConeSndElement A D f) w (add_zero n)) : z = w := by
  apply moduleHomElement_ext A D
  intro x
  apply (mappingCone.ext_cochain_to_iff ((moduleEvaluation A D x).map f) n (n + 1) rfl).2
  constructor
  · have h := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f (n + 1)) hfst
    simpa only [moduleHomCompose_π, moduleConeFstElement_π] using h
  · have h := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f n) hsnd
    simpa only [moduleHomCompose_π, moduleConeSndElement_π] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
