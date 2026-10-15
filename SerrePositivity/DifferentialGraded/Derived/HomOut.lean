module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Evaluation

/-! # 射影的始域からの全Homの指定導来局所化への延長

値域は宇宙wを指定した既存D(A)。始域変数の選択独立性は後続で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleHomOutToDerived (T : ModuleCategory A D) :
    ModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  eCoyoneda (Complex A) T ⋙ DerivedCategory.Q

lemma moduleHomOutToDerived_inverts (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) :
    (moduleQuasiIso A D).IsInvertedBy (moduleHomOutToDerived A D T) := by
  intro M N f hf
  have : QuasiIso (eHomWhiskerLeft (Complex A) T f) :=
    moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf
  change IsIso (DerivedCategory.Q.map (eHomWhiskerLeft (Complex A) T f))
  infer_instance

def moduleDerivedHomOut (T : ModuleCategory A D) (hT : moduleHomotopicallyProjective A D T) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedLift A D (moduleHomOutToDerived A D T) (moduleHomOutToDerived_inverts A D T hT)

lemma moduleDerivedHomOut_fac (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) :
    moduleToDerived A D ⋙ moduleDerivedHomOut A D T hT = moduleHomOutToDerived A D T :=
  moduleDerivedLift_fac A D _ _

def moduleDerivedHomOutComputation (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) (N : ModuleCategory A D) :
    (moduleDerivedHomOut A D T hT).obj ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj (moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N)) :=
  eqToIso (congrArg (fun F => F.obj N) (moduleDerivedHomOut_fac A D T hT))

def moduleResolvedHomOut (M : ModuleCategory A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedHomOut A D (moduleResolutionCandidate A D M)
    (moduleSemifree_homotopicallyProjective A D (moduleResolutionCandidate_semifree A D M))

end SerrePositivity.DifferentialGraded
