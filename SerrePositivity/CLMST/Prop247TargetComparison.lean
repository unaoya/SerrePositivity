module

public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationCompletedBaseChange
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidCompletedBaseChangeDiscrete

/-! # Prop 2.4.7：終域の実完備導来底変換と perfectoid 化

既存 BS の環版底変換比較と実完備 tensor の離散性を使う。
H⁰ の B 線形同型を実導来対象全体へ持ち上げ、元の環写像との可換式を保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S B C P : Type u) [CommRing R] [CommRing S] [CommRing B]
    [CommRing C] [CommRing P] [Algebra R S] [Algebra R B] [Algebra R C] [Algebra B P]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (β : B ⊗[R] S →ₐ[B] P) (hβ : IsPerfectoidization p β.toRingHom)
local notation "AC" => boundedAboveCompletedTensorAlgebra R (p : R) B C
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AC).X.obj

/-- 元の通常 tensor からの写像を保つ、BS 環版の B 代数比較。 -/
def prop247_targetTensorAlgEquiv :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    letI := completedTensorH0LeftAlgebra R (p : R) B C
    H ≃ₐ[B] P := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) B C
  exact (BhattScholze.perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p B S C hR hB f hf P β hβ).choose

/-- 比較は BS が構成した元の通常 tensor の標準射と可換。 -/
theorem prop247_targetTensorAlgEquiv_comp :
    let := derivedH0CommRing AC
    let := derivedH0Algebra AC
    let := completedTensorH0LeftAlgebra R (p : R) B C
    (prop247_targetTensorAlgEquiv R S B C P p hR hB f hf β hβ).toRingHom.comp
      (BhattScholze.perfectoidizationCompletedBaseChangeMap R p B S C f) = β.toRingHom := by
  let := derivedH0CommRing AC
  let := derivedH0Algebra AC
  let := completedTensorH0LeftAlgebra R (p : R) B C
  exact (BhattScholze.perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p B S C hR hB f hf P β hβ).choose_spec

/-- 元の B 作用を保持した、実完備底変換の H⁰ 比較。 -/
def prop247_targetH0LinearEquiv :
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj) ≃ₗ[B] P := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) B C
  exact (completedBaseChangeTensorH0LinearEquiv R B C (p : R)).trans
    (prop247_targetTensorAlgEquiv R S B C P p hR hB f hf β hβ).toLinearEquiv

/-- 完備 tensor の離散性を用いた、終域の実導来対象全体の比較。 -/
def prop247_targetCompletedBaseChangeIso :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B P) := by
  let Y := (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
    ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj
  have hp := BhattScholze.integralPerfectoid_completedBaseChange_pure p R B C hR hB hf.1
  have : Y.IsGE 0 := by
    dsimp only [Y]
    rw [map_natCast]
    exact hp.1
  have : Y.IsLE 0 := by
    dsimp only [Y]
    rw [map_natCast]
    exact hp.2
  exact normalizedPureHomologyIso Y 0 ≪≫ (moduleObjectFunctor B).mapIso
    (prop247_targetH0LinearEquiv R S B C P p hR hB f hf β hβ).toModuleIso

/-- 終域全体の同型は、選択した環版比較からの元の H⁰ 線形同値を誘導する。 -/
theorem prop247_targetCompletedBaseChangeIso_homology :
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
        (prop247_targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).hom.app
        (ModuleCat.of B P) =
      (prop247_targetH0LinearEquiv R S B C P p hR hB f hf β hβ).toModuleIso.hom := by
  let Y := (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
    ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj
  have hp := BhattScholze.integralPerfectoid_completedBaseChange_pure p R B C hR hB hf.1
  have : Y.IsGE 0 := by dsimp only [Y]; rw [map_natCast]; exact hp.1
  have : Y.IsLE 0 := by dsimp only [Y]; rw [map_natCast]; exact hp.2
  let e := (prop247_targetH0LinearEquiv R S B C P p hR hB f hf β hβ).toModuleIso
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0
  have hn := ε.hom.naturality e.hom
  change H₀.map ((moduleObjectFunctor B).map e.hom) ≫ ε.hom.app (ModuleCat.of B P) =
    ε.hom.app (H₀.obj Y) ≫ e.hom at hn
  change H₀.map ((normalizedPureHomologyIso Y 0).hom ≫
      (moduleObjectFunctor B).map e.hom) ≫ ε.hom.app (ModuleCat.of B P) = e.hom
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    normalizedPureHomologyIso_homology, Category.id_comp]

end SerrePositivity.CLMST
