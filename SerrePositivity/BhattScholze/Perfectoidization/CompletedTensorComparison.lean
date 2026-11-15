module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChange
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChange

/-! # 完備な導来基底変更と perfectoid 化の比較

## 概要

元の完備な基底変更の単位と BS の通常のテンソルの写像が一致することを示し（`completedBaseChangeTensorH0_unit`）、終域の完備な導来基底変更の零次と perfectoid 化の代数同型（`targetTensorAlgEquiv`）、その `H⁰` の線形同型を導来対象全体の同型へ持ち上げる（`targetCompletedBaseChangeIso`）。
BS 著者版 Proposition 8.13 の環版に向けて、完備導来底変換と perfectoid 化を比較する。

## 方針

BS の環版の基底変更の比較と、完備なテンソルの離散性を使う。元の環写像との可換性を保つ。

## 規約

単位の一致には perfectoid 性・平坦性・有限性は要らない。旧 `CLMST/Prop247TensorUnit`・`Prop247TargetComparison`（`prop247_` を外した）。`targetTensorAlgEquiv` は `.choose` でデータを作っている（一意存在から選んだ比較データ）。

## 使われ方

CLMST の `PerfectoidizationIsogeny`（Prop 2.4.7）の標準の四角。
-/

@[expose] public noncomputable section

universe u

section TensorUnitPart

namespace SerrePositivity.BhattScholze
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (p : ℕ)

/-- 元の完備底変換単位は、元の B 線形 H⁰ 比較を通して BS の通常 tensor 写像となる。 -/
theorem completedBaseChangeTensorH0_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) B S)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) B S)
    letI := completedTensorH0LeftAlgebra R (p : R) B S
    completedBaseChangeTensorH0LinearEquiv R B S (p : R)
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B (p : R))).app
            ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) x) =
      BhattScholze.completedTensorPerfectoidizationMap R p B S
        ((algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom
          ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
            (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) B S)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) B S)
  let := completedTensorH0LeftAlgebra R (p : R) B S
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) B S)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) B S)
  rw [completedBaseChangeTensorH0LinearEquiv_apply, completedBaseChangeTensorH0Iso_unit_apply,
    BhattScholze.completedTensorPerfectoidizationMap_apply, derivedH0AlgMap_apply,
    boundedAboveCompletionAlgebraUnit_hom]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R (p : R)).app
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj)
      ((algebraBaseChangeTensorH0Iso R B S).hom x) =
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R (p : R)).app
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj) _
  apply congrArg
  apply (derivedTensorH0AlgEquiv (R := R) B S).injective
  rw [AlgEquiv.apply_symm_apply]
  exact algebraBaseChangeTensorH0Iso_apply R B S x

end SerrePositivity.BhattScholze

end TensorUnitPart

section TargetComparisonPart

namespace SerrePositivity.BhattScholze
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
def targetTensorAlgEquiv :
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
theorem targetTensorAlgEquiv_comp :
    let := derivedH0CommRing AC
    let := derivedH0Algebra AC
    let := completedTensorH0LeftAlgebra R (p : R) B C
    (targetTensorAlgEquiv R S B C P p hR hB f hf β hβ).toRingHom.comp
      (BhattScholze.perfectoidizationCompletedBaseChangeMap R p B S C f) = β.toRingHom := by
  let := derivedH0CommRing AC
  let := derivedH0Algebra AC
  let := completedTensorH0LeftAlgebra R (p : R) B C
  exact (BhattScholze.perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p B S C hR hB f hf P β hβ).choose_spec

/-- 元の B 作用を保持した、実完備底変換の H⁰ 比較。 -/
def targetH0LinearEquiv :
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj) ≃ₗ[B] P := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) B C
  exact (completedBaseChangeTensorH0LinearEquiv R B C (p : R)).trans
    (targetTensorAlgEquiv R S B C P p hR hB f hf β hβ).toLinearEquiv

/-- 完備 tensor の離散性を用いた、終域の実導来対象全体の比較。 -/
def targetCompletedBaseChangeIso :
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
    (targetH0LinearEquiv R S B C P p hR hB f hf β hβ).toModuleIso

/-- 終域全体の同型は、選択した環版比較からの元の H⁰ 線形同値を誘導する。 -/
theorem targetCompletedBaseChangeIso_homology :
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
        (targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).hom.app
        (ModuleCat.of B P) =
      (targetH0LinearEquiv R S B C P p hR hB f hf β hβ).toModuleIso.hom := by
  let Y := (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
    ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj
  have hp := BhattScholze.integralPerfectoid_completedBaseChange_pure p R B C hR hB hf.1
  have : Y.IsGE 0 := by dsimp only [Y]; rw [map_natCast]; exact hp.1
  have : Y.IsLE 0 := by dsimp only [Y]; rw [map_natCast]; exact hp.2
  let e := (targetH0LinearEquiv R S B C P p hR hB f hf β hβ).toModuleIso
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0
  have hn := ε.hom.naturality e.hom
  change H₀.map ((moduleObjectFunctor B).map e.hom) ≫ ε.hom.app (ModuleCat.of B P) =
    ε.hom.app (H₀.obj Y) ≫ e.hom at hn
  change H₀.map ((normalizedPureHomologyIso Y 0).hom ≫
      (moduleObjectFunctor B).map e.hom) ≫ ε.hom.app (ModuleCat.of B P) = e.hom
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    normalizedPureHomologyIso_homology, Category.id_comp]

end SerrePositivity.BhattScholze

end TargetComparisonPart
