module
public import SerrePositivity.DifferentialGraded.Module.TensorSource
public import SerrePositivity.DifferentialGraded.Module.TensorUnit

/-! # パラメータ付きHom endの転置と加群変数の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- tensor加群からの射を主Hom endへのchain mapへ転置する。 -/
def moduleParamCurry {K : Complex A} {M N : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) :
    K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) :=
  (moduleHomEquiv A D K _ _).symm
    (tensorFamilyCurry A (K := K) (M := ForgetEnrichment.to (Complex A) M)
      (N := ForgetEnrichment.to (Complex A) N)
      (closedTransApp A (moduleClosedHomEquiv A D (moduleTensorLeftObj A D K M) N f))
      (closedTransApp_naturality A
        (moduleClosedHomEquiv A D (moduleTensorLeftObj A D K M) N f)))

@[reassoc] lemma moduleParamCurry_π {K : Complex A} {M N : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) (x : D) :
    moduleParamCurry A D f ≫
        moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x =
      curryRight ((moduleEvaluation A D x).map f) := by
  unfold moduleParamCurry
  rw [moduleHomEquiv_symm_π]
  rfl

@[simp] lemma moduleParamUncurry_curry {K : Complex A} {M N : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) :
    moduleParamUncurry A D (moduleParamCurry A D f) = f := by
  apply moduleMorphism_ext
  intro x
  rw [moduleParamUncurry_eval, moduleParamCurry_π, uncurryRight_curryRight]

@[simp] lemma moduleParamCurry_uncurry {K : Complex A} {M N : ModuleCategory A D}
    (a : K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)) :
    moduleParamCurry A D (moduleParamUncurry A D a) = a := by
  apply moduleHom_ext
  intro x
  rw [moduleParamCurry_π, moduleParamUncurry_eval, curryRight_uncurryRight]
  simp only [ForgetEnrichment.to_of]

lemma moduleParamUncurry_injective {K : Complex A} {M N : ModuleCategory A D}
    {a b : K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)}
    (h : moduleParamUncurry A D a = moduleParamUncurry A D b) : a = b := by
  have hh := congrArg (moduleParamCurry A D) h
  simpa only [moduleParamCurry_uncurry] using hh

/-- 加群変数への前合成と逆転置の整合性。 -/
lemma moduleParamUncurry_naturality_source {K : Complex A} {M P N : ModuleCategory A D}
    (f : M ⟶ P) (a : K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N)) :
    moduleTensorLeftMap A D K f ≫ moduleParamUncurry A D a =
      moduleParamUncurry A D (a ≫ eHomWhiskerRight (Complex A) f N) := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleTensorLeftMap_eval,
    moduleParamUncurry_eval, moduleParamUncurry_eval]
  have hπ := congrArg (fun b => a ≫ b) (moduleHomWhiskerRight_π A D f x (P := N))
  rw [← Category.assoc] at hπ
  change (𝟙 K ⊗ₘ (moduleEvaluation A D x).map f) ≫
    uncurryRight (a ≫ moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N) x) =
    uncurryRight ((a ≫ eHomWhiskerRight (Complex A) f N) ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x)
  refine Eq.trans ?_ (congrArg uncurryRight hπ.symm)
  apply (tensorRightHomEquiv _ _ _).injective
  change curryRight ((𝟙 K ⊗ₘ (moduleEvaluation A D x).map f) ≫ uncurryRight _) =
    curryRight (uncurryRight _)
  rw [curryRight_naturality_domain, curryRight_uncurryRight, curryRight_uncurryRight,
    Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded
