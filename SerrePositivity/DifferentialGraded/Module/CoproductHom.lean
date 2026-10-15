module
public import SerrePositivity.DifferentialGraded.Module.ParamCurry

/-! # 余積を源とする全次数Hom endの直積表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

abbrev moduleCoproductHomFamily (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    J → Complex A :=
  fun j => moduleHom A D (ForgetEnrichment.to (Complex A) (M j)) (ForgetEnrichment.to (Complex A) N)

def moduleCoproductHomFan (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    Fan (moduleCoproductHomFamily A D M N) :=
  Fan.mk (moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M)) (ForgetEnrichment.to (Complex A) N))
    (fun j => eHomWhiskerRight (Complex A) (Sigma.ι M j) N)

/-- tensorの余積保存と各成分の逆転置によるHomへのlift。 -/
def moduleCoproductHomLift (M : J → ModuleCategory A D) (N : ModuleCategory A D)
    (c : Fan (moduleCoproductHomFamily A D M N)) :
    c.pt ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M))
      (ForgetEnrichment.to (Complex A) N) :=
  moduleParamCurry A D
    (Cofan.IsColimit.desc
      (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
      (fun j => moduleParamUncurry A D (c.proj j)))

lemma moduleCoproductHomLift_π (M : J → ModuleCategory A D) (N : ModuleCategory A D)
    (c : Fan (moduleCoproductHomFamily A D M N)) (j : J) :
    moduleCoproductHomLift A D M N c ≫ eHomWhiskerRight (Complex A) (Sigma.ι M j) N = c.proj j := by
  apply moduleParamUncurry_injective A D (M := M j) (N := N)
  have hn := moduleParamUncurry_naturality_source A D (Sigma.ι M j)
    (moduleCoproductHomLift A D M N c)
  have hu : moduleParamUncurry A D (moduleCoproductHomLift A D M N c) =
      Cofan.IsColimit.desc
        (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
        (fun t => moduleParamUncurry A D (c.proj t)) :=
    moduleParamUncurry_curry A D _
  have hf : moduleTensorLeftMap A D c.pt (Sigma.ι M j) ≫
      Cofan.IsColimit.desc
        (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
        (fun t => moduleParamUncurry A D (c.proj t)) = moduleParamUncurry A D (c.proj j) :=
    Cofan.IsColimit.fac
      (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M) _ j
  exact hn.symm.trans
    ((congrArg (fun b => moduleTensorLeftMap A D c.pt (Sigma.ι M j) ≫ b) hu).trans hf)

/-- Hom endの標準射影が、真の直積を与える。 -/
def moduleCoproductHomIsLimit (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    IsLimit (moduleCoproductHomFan A D M N) :=
  Fan.IsLimit.mk _ (moduleCoproductHomLift A D M N)
    (fun c j => moduleCoproductHomLift_π A D M N c j) (by
      intro c a ha
      apply moduleParamUncurry_injective A D (M := ∐ M) (N := N)
      unfold moduleCoproductHomLift
      rw [moduleParamUncurry_curry]
      apply Cofan.IsColimit.hom_ext
        (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
      intro j
      simp only [cofan_mk_inj]
      have hn := moduleParamUncurry_naturality_source A D (Sigma.ι M j)
        (show c.pt ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M))
          (ForgetEnrichment.to (Complex A) N) from a)
      have hj : a ≫ eHomWhiskerRight (Complex A) (Sigma.ι M j) N = c.proj j := ha j
      exact (hn.trans (congrArg (moduleParamUncurry A D) hj)).trans
        (Cofan.IsColimit.fac
          (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
          (fun t => moduleParamUncurry A D (c.proj t)) j).symm)


/-- 全次数dg自然性と微分を保つchain iso。 -/
def moduleCoproductHomIso (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M)) (ForgetEnrichment.to (Complex A) N) ≅
      ∏ᶜ moduleCoproductHomFamily A D M N :=
  IsLimit.conePointUniqueUpToIso (moduleCoproductHomIsLimit A D M N) (productIsProduct _)

@[reassoc] lemma moduleCoproductHomIso_hom_π (M : J → ModuleCategory A D)
    (N : ModuleCategory A D) (j : J) :
    (moduleCoproductHomIso A D M N).hom ≫ Pi.π (moduleCoproductHomFamily A D M N) j =
      eHomWhiskerRight (Complex A) (Sigma.ι M j) N :=
  IsLimit.conePointUniqueUpToIso_hom_comp (moduleCoproductHomIsLimit A D M N)
    (productIsProduct _) ⟨j⟩

end SerrePositivity.DifferentialGraded
