module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensor

/-! # 導来係数変更と coend 計算モデルの自然性・単位・結合

一般のモデルでは比較射、A-K-flat な coend では比較同型となる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 選んだ coend モデルの導来係数変更比較。 -/
def derivedBalancedComparison (M : RightModule A D) (N : LeftModule A D) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj (BalancedTensor.obj A D M N)) ⟶
      DerivedCategory.Q.obj (BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D M) (leftModule φ D N)) :=
  (complexDerivedExtensionAugmentation φ).app (BalancedTensor.obj A D M N) ≫
    DerivedCategory.Q.map (balancedIso φ D M N).hom

lemma derivedBalancedComparison_isIso (M : RightModule A D) (N : LeftModule A D)
    (hMN : complexKFlat A (BalancedTensor.obj A D M N)) :
    IsIso (derivedBalancedComparison φ D M N) := by
  have := complexDerivedExtensionAugmentation_isIso φ _ hMN
  unfold derivedBalancedComparison
  infer_instance

lemma derivedBalancedComparison_naturality {M M' : ModuleCategory A D}
    {N N' : LeftModuleCategory A D} (f : M ⟶ M') (g : N ⟶ N') :
    (complexDerivedExtension φ).map (DerivedCategory.Q.map (BalancedTensor.map A D f g)) ≫
        derivedBalancedComparison φ D (ForgetEnrichment.to (Complex A) M')
          (ForgetEnrichment.to (Complex A) N') =
      derivedBalancedComparison φ D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) ≫
          DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
            ((moduleExtension φ D).map f) ((leftModuleExtension φ D).map g)) := by
  unfold derivedBalancedComparison
  have hn := (complexDerivedExtensionAugmentation φ).naturality (BalancedTensor.map A D f g)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [balancedIso_module_naturality φ D f g]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- 右 representable の評価単位との可換図式。 -/
lemma derivedBalancedComparison_yoneda (z : D) (N : LeftModule A D) :
    derivedBalancedComparison φ D (representable A z) N ≫
        DerivedCategory.Q.map (yonedaBaseChangeIso φ D z N).hom =
      (complexDerivedExtension φ).map (DerivedCategory.Q.map
        (BalancedTensor.yonedaIso A D z N).hom) ≫
          (complexDerivedExtensionAugmentation φ).app (N.obj z) := by
  unfold derivedBalancedComparison
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, yonedaBaseChange_comparison]
  exact ((complexDerivedExtensionAugmentation φ).naturality
    (BalancedTensor.yonedaIso A D z N).hom).symm

/-- 左 representable の評価単位との可換図式。 -/
lemma derivedBalancedComparison_leftYoneda (z : D) (M : RightModule A D) :
    derivedBalancedComparison φ D M (leftRepresentable A z) ≫
        DerivedCategory.Q.map (leftYonedaBaseChangeIso φ D z M).hom =
      (complexDerivedExtension φ).map (DerivedCategory.Q.map
        (BalancedTensor.leftYonedaIso A D z M).hom) ≫
          (complexDerivedExtensionAugmentation φ).app (M.obj (Opposite.op z)) := by
  unfold derivedBalancedComparison
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, leftYonedaBaseChange_comparison]
  exact ((complexDerivedExtensionAugmentation φ).naturality
    (BalancedTensor.leftYonedaIso A D z M).hom).symm

/-- 複体パラメータの結合比較との可換図式。 -/
lemma derivedBalancedComparison_tensorModule (K : Complex A)
    (M : RightModule A D) (N : LeftModule A D) :
    derivedBalancedComparison φ D (tensorModule K M) N ≫
        DerivedCategory.Q.map (tensorModuleBaseChangeIso φ D K M N).hom =
      (complexDerivedExtension φ).map (DerivedCategory.Q.map
        (BalancedTensor.tensorModuleIso A D K M N).hom) ≫
          (complexDerivedExtensionAugmentation φ).app (K ⊗ BalancedTensor.obj A D M N) ≫
            DerivedCategory.Q.map ((tensorIso φ K (BalancedTensor.obj A D M N)).hom ≫
              (extension φ).obj K ◁ (balancedIso φ D M N).hom) := by
  unfold derivedBalancedComparison
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, tensorModuleBaseChange_comparison,
    CategoryTheory.Functor.map_comp, ← Category.assoc]
  have hn := (complexDerivedExtensionAugmentation φ).naturality
    (BalancedTensor.tensorModuleIso A D K M N).hom
  simp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc]

end SerrePositivity.DifferentialGraded.ScalarExtension
