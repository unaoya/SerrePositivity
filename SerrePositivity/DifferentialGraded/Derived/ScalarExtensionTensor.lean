module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplexNaturality
public import SerrePositivity.DifferentialGraded.Derived.RightTensorResolution

/-! # K-flat 計算モデルによる導来 tensor の係数変更

選んだ右射影解像度 P について、P ⊗ N の A 上 K-flat 性と、
係数変更した P の相対 K-flat 性を明示的に受け取る。
これらを A′ の A-flat 性や任意の dg 圏に対する自動的な性質に置き換えない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

section
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

omit φ in
/-- 相対 K-flat な右加群では導来 tensor を underived に計算する。 -/
def relativeKFlatTensorComputation (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (N : LeftModule A D) :
    (moduleDerivedTensorRight A D N).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) M) N) := by
  let P := moduleCanonicalProjectiveResolution A D M
  have hP : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P.obj) :=
    moduleSemifree_relativeKFlat A D (moduleResolutionCandidate_semifree A D M)
  have : QuasiIso ((BalancedTensor.rightTensorFunctor A D N).map P.π) :=
    BalancedTensor.rightTensor_relativeKFlat_quasiIso A D N hP hM P.π P.quasiIso
  exact moduleResolutionDerivedTensorComputation A D
    (moduleCanonicalProjectiveResolution A D) N M ≪≫
      asIso (DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D N).map P.π))

end

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 導来係数変更と相対 tensor の比較。
左因子 N は、明示した K-flat 計算条件を満たす選択済みモデルとして扱う。 -/
def derivedTensorBaseChange {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : LeftModule A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) P.obj) N))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) P.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedTensorRight A D N).obj ((moduleToDerived A D).obj M)) ≅
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D N)).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) :=
  (complexDerivedExtension φ).mapIso (moduleDerivedTensorRightResolutionComputation A D P N) ≪≫
    complexDerivedExtensionKFlatIso φ _ hPN ≪≫
    DerivedCategory.Q.mapIso (balancedIso φ D (ForgetEnrichment.to (Complex A) P.obj) N) ≪≫
    (relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj P.obj)
      hP' (leftModule φ D N)).symm ≪≫
    (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D N)).mapIso
      (derivedExtensionResolutionComputation φ D P).symm

omit [HasDerivedCategory (ModuleCat.{u} A)] in
/-- 係数変更後の coend 計算も両変数の全 dg 自然な射に自然。 -/
lemma derivedBalancedIso_naturality {M M' : ModuleCategory A D}
    {N N' : LeftModuleCategory A D} (f : M ⟶ M') (g : N ⟶ N') :
    DerivedCategory.Q.map ((extension φ).map (BalancedTensor.map A D f g)) ≫
        (DerivedCategory.Q.mapIso (balancedIso φ D
          (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N'))).hom =
      (DerivedCategory.Q.mapIso (balancedIso φ D
        (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))).hom ≫
          DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
            ((moduleExtension φ D).map f) ((leftModuleExtension φ D).map g)) := by
  simp only [Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (balancedIso_module_naturality φ D f g)

end SerrePositivity.DifferentialGraded.ScalarExtension
