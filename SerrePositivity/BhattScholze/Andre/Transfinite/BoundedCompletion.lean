module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeScalar
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTensor
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionBounded
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedTorsionComparison
open SerrePositivity SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (a : R) (n : ℕ) (b : R)
/-- ## 概要
主元 b のイデアルが a の冪を含めば、a に沿う導来完備化の単位は R/(b) への導来底変換で同型になる。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
R/(b) の導来対象が a の冪で消えることを使い、元の完備化単位をその対象とテンソルする。
導来底変換とテンソルの自然同型および制限スカラーの同型反映性を使う。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
theorem derivedCompletion_quotient_unit_isIso_of_power_mem
    (hb : a ^ n ∈ Ideal.span {b}) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    IsIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).map
      ((boundedAboveDerivedCompletionUnit R a).app X)) := by
  let f := (boundedAboveDerivedCompletionUnit R a).app X
  let Y := derivedBaseChangeScalarObject (Ideal.Quotient.mk (Ideal.span {b}))
  have hz : (Ideal.Quotient.mk (Ideal.span {b})) (a ^ n) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hb
  have hmod : a ^ n • 𝟙 (baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {b}))) = 0 := by
    rw [← restrictedScalarMultiplication_algebraMap, hz]
    simp [restrictedScalarMultiplication]
  have hY : a ^ n • 𝟙 Y = 0 := by
    apply InducedCategory.hom_ext
    change a ^ n • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
      (baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {b})))) = 0
    have hs := congrArg (DerivedCategory.singleFunctor (ModuleCat R) 0).map hmod
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] using hs
  have hi : IsIso (f ▷ Y) := completionUnit_tensor_powerTorsion_isIso R a X Y n hY
  have hn := BraidedCategory.braiding_naturality_right Y f
  have hleft : IsIso (Y ◁ f) := by
    have : IsIso ((Y ◁ f) ≫ (β_ Y _).hom) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (β_ Y _).hom
  have hn' := boundedAboveDerivedBaseChangeTensorIso_naturality
    (Ideal.Quotient.mk (Ideal.span {b})) f
  have : IsIso ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {b}))).map
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).map f) ≫
        (boundedAboveDerivedBaseChangeTensorIso (Ideal.Quotient.mk (Ideal.span {b})) _).hom) := by
    rw [hn']
    exact inferInstanceAs (IsIso ((boundedAboveDerivedBaseChangeTensorIso
      (Ideal.Quotient.mk (Ideal.span {b})) _).hom ≫ Y ◁ f))
  have : IsIso ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {b}))).map
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).map f)) :=
    IsIso.of_isIso_comp_right _ (boundedAboveDerivedBaseChangeTensorIso
      (Ideal.Quotient.mk (Ideal.span {b})) _).hom
  exact isIso_of_reflects_iso _
    (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {b})))


/-- ## 概要
係数環 R 自身の導来 a 進完備化を R/(a) に導来底変換すると、元の剰余環の離散対象と同型になる。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
前補題を n=1 に適用し、R 自身の射影性から通常の剰余対象へ移す。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
def completedUnitReductionIso :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj
      ((boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))) ≅
      boundedAboveDerivedSingleFunctor.obj
        ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
          (ModuleCat.of R R)) := by
  let X0 := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)
  let q1 := Ideal.Quotient.mk (Ideal.span {a})
  have hTor : scalarExtensionTorVanishing q1 (ModuleCat.of R R) := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact isZero_Tor_succ_of_projective (ModuleCat.{u} R) (baseChangeScalarModule q1)
      (ModuleCat.of R R) m
  have hunit : IsIso ((boundedAboveDerivedBaseChange q1).map
      ((boundedAboveDerivedCompletionUnit R a).app X0)) := by
    exact derivedCompletion_quotient_unit_isIso_of_power_mem R a 1 a (by simp) X0
  exact (asIso ((boundedAboveDerivedBaseChange q1).map
      ((boundedAboveDerivedCompletionUnit R a).app X0))).symm ≪≫
    boundedAboveDerivedBaseChangeModuleAugmentationIso q1 (ModuleCat.of R R) hTor

variable (hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
include hbound in
/-- ## 概要
a 冪ねじれが有界な環では、R 自身の導来 a 進完備化は次数 0 に集中し、その零次ホモロジーの a 冪ねじれも有界である。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
実際の剰余への導来底変換が離散かつ平坦であることを示し、既存の有界ねじれ純性定理を適用する。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
theorem completedUnit_pure_bounded_torsion :
    let X := (boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ n : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj,
          a ^ n • z = 0 → a ^ N • z = 0 := by
  let X0 := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)
  let X := (boundedAboveDerivedCompletionFunctor R a).obj X0
  let q1 := Ideal.Quotient.mk (Ideal.span {a})
  let e := completedUnitReductionIso R a
  have hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange q1).obj X).obj) := by
    intro i hi
    exact (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).mapIso
        (DerivedCategory.Minus.ι.mapIso e))
  have hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange q1).obj X).obj) := by
    let E := (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso e) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (R ⧸ Ideal.span {a})) 0).app _
    let := q1.toAlgebra
    have hf : Module.Flat (R ⧸ Ideal.span {a})
        ((ModuleCat.extendScalars q1).obj (ModuleCat.of R R)) := by
      exact Module.Flat.of_linearEquiv
        (TensorProduct.AlgebraTensorModule.rid R (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}))
    exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr hf
  exact derived_pure_bounded_torsion_of_complete_flat_reduction a X hPure hFlat
    hbound (derivedComplexCompletionFunctor_isComplete R a X0.obj)

include hbound in
/-- ## 概要
有界 a 冪ねじれの下で、実際の導来主イデアル完備化の零次ホモロジーは古典的に a 進完備である。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
前補題のねじれ境界を既存の主イデアル Koszul ホモロジーへ移し、導来完備性と有界ねじれから古典的完備性を得る。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
theorem principalCompletionH0_isAdicComplete_of_bounded_torsion :
    IsAdicComplete (Ideal.span {a}) (PrincipalCompletionH0 R a) := by
  let X0 := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)
  let X := (boundedAboveDerivedCompletionFunctor R a).obj X0
  obtain ⟨_, _, N, hN⟩ := completedUnit_pure_bounded_torsion R a hbound
  apply isAdicComplete_of_isModuleComplete_of_bounded_torsion R a _
    (principalCompletionH0_isModuleComplete R a)
  let eH := (principalCompletedUnitH0Iso R a).toLinearEquiv
  change ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj) ≃ₗ[R]
    PrincipalCompletionH0 R a at eH
  refine ⟨N, ?_⟩
  intro k x hx
  apply eH.symm.injective
  rw [map_smul, map_zero]
  apply hN k
  rw [← map_smul, hx, map_zero]


/-- ## 概要
有界 a 冪ねじれの下で、実際の導来完備化を既存の主イデアル完備化 H0 の離散対象と同定する。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
次数 0 集中から規格化されたホモロジー同型を使い、既存の H0 比較を合成する。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
def completedUnitPrincipalH0Iso :
    (boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)) ≅
      boundedAboveDerivedSingleFunctor.obj (PrincipalCompletionH0 R a) := by
  let X := (boundedAboveDerivedCompletionFunctor R a).obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))
  obtain ⟨hGE, hLE, _⟩ := completedUnit_pure_bounded_torsion R a hbound
  let := hGE
  let := hLE
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj 0 ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso (principalCompletedUnitH0Iso R a))

/-- ## 概要
有界 a 冪ねじれの下で、主イデアル完備化 H0 の実導来剰余は元の環の通常剰余となる。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
H0 の離散対象を実導来完備化へ戻し、元の完備化単位に沿う導来剰余同型を合成する。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
def principalCompletionH0DerivedReductionIso :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj
      (boundedAboveDerivedSingleFunctor.obj (PrincipalCompletionH0 R a)) ≅
      boundedAboveDerivedSingleFunctor.obj
        ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj (ModuleCat.of R R)) :=
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).mapIso
    (completedUnitPrincipalH0Iso R a hbound).symm ≪≫ completedUnitReductionIso R a

/-- ## 概要
主イデアル完備化 H0 の通常剰余を元の通常剰余と、R/(a) 線形に比較する。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
実導来剰余比較の零次ホモロジーを取り、通常の係数拡大との標準比較を両端で使う。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
def principalCompletionH0ReductionEquiv :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj
      (PrincipalCompletionH0 R a)) ≃ₗ[R ⧸ Ideal.span {a}]
      (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a}))).obj (ModuleCat.of R R) := by
  let q1 := Ideal.Quotient.mk (Ideal.span {a})
  exact ((boundedAboveDerivedBaseChangeModuleH0Iso q1).app (PrincipalCompletionH0 R a)).symm.trans
    ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (principalCompletionH0DerivedReductionIso R a hbound)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat (R ⧸ Ideal.span {a})) 0).app _)
    |>.toLinearEquiv

include hbound in
/-- ## 概要
有界 a 冪ねじれの下で、主イデアル完備化 H0 と R/(a) のすべての正次数 Tor は零となる。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
実際の導来剰余の離散性を、標準の負次数ホモロジーと Tor の比較で移す。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
theorem principalCompletionH0_scalarExtensionTorVanishing :
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {a}))
    (PrincipalCompletionH0 R a) := by
  intro k hk
  let q1 := Ideal.Quotient.mk (Ideal.span {a})
  have hz : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (R ⧸ Ideal.span {a})) (-(k : ℤ))).obj
      ((boundedAboveDerivedBaseChange q1).obj
        (boundedAboveDerivedSingleFunctor.obj (PrincipalCompletionH0 R a))).obj) :=
    (derivedSingleHomology_isZero _ _ (by omega)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) (-(k : ℤ))).mapIso
        (DerivedCategory.Minus.ι.mapIso (principalCompletionH0DerivedReductionIso R a hbound)))
  exact ((ModuleCat.restrictScalars q1).map_isZero hz).of_iso
    ((boundedAboveDerivedBaseChangeModuleTorIso q1 k).app (PrincipalCompletionH0 R a)).symm

include hbound in
/-- ## 概要
有界 a 冪ねじれの下で、主イデアル完備化 H0 は元の環上 a 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
剰余 Tor の消滅と、R/(a) 線形な通常剰余同型による忠実平坦性を、
既存の完全平坦性判定に入力する。

## 規約
a は任意の環の元。a 正則性や Noether 性は仮定しない。

## 使われ方
通常完備化との代数同型によって、完備化の完全忠実平坦性を導く。
-/
theorem principalCompletionH0_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat (Ideal.span {a}) (PrincipalCompletionH0 R a) := by
  let Q := R ⧸ Ideal.span {a}
  let q1 := Ideal.Quotient.mk (Ideal.span {a})
  let := q1.toAlgebra
  let eR := TensorProduct.AlgebraTensorModule.rid R Q Q
  have hfR : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q1).obj (ModuleCat.of R R)) :=
    Module.FaithfullyFlat.of_linearEquiv Q Q eR
  let e := principalCompletionH0ReductionEquiv R a hbound
  have hf : Module.FaithfullyFlat Q
      ((ModuleCat.extendScalars q1).obj (PrincipalCompletionH0 R a)) :=
    Module.FaithfullyFlat.of_linearEquiv Q _ e
  have hc : IsCompletelyFlat (Ideal.span {a}) (PrincipalCompletionH0 R a) :=
    isCompletelyFlat_of_acyclic_flat_reduction _ _
      (principalCompletionH0_scalarExtensionTorVanishing R a hbound) hf.1
  let et := (quotientScalarExtensionEquiv (Ideal.span {a}) (PrincipalCompletionH0 R a)).trans
    (quotientTensorReductionEquiv (Ideal.span {a}) (PrincipalCompletionH0 R a)).symm
  exact ⟨hc, Module.FaithfullyFlat.of_linearEquiv Q _ et.symm⟩


/-- ## 概要
有界 a 冪ねじれの下で、実主イデアル完備化の H0 と通常の a 進完備化は、元の R 作用を保つ代数同型を持つ。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
古典的完備性を得た H0 へ通常完備化の普遍性を使う。逆射は実 H0 の普遍性から得て、
二つの普遍性で両合成が恒等であることを検証する。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
def boundedPrincipalCompletionAdicAlgEquiv :
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PrincipalCompletionH0 R a ≃ₐ[R] AdicCompletion (Ideal.span {a}) R := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let := principalCompletionH0_isAdicComplete_of_bounded_torsion R a hbound
  let := AdicCompletion.isAdicComplete (R := R) (M := R)
    (Submodule.fg_span (Set.toFinite ({a} : Set R)))
  let i := adicCompletionToCompleteAlgebra R (Ideal.span {a})
    (Submodule.fg_span (Set.toFinite _)) (PrincipalCompletionH0 R a)
  let b := principalCompletionToAdic R a
  have hbi : b.comp i = AlgHom.id R (AdicCompletion (Ideal.span {a}) R) :=
    adicCompletion_algHom_ext R (Ideal.span {a}) (Submodule.fg_span (Set.toFinite _)) _ _ _
  have hib : i.comp b = AlgHom.id R (PrincipalCompletionH0 R a) :=
    (principalCompletion_existsUnique_algHom R a (PrincipalCompletionH0 R a)
      (principalCompletionH0_isModuleComplete R a)).unique trivial trivial
  exact AlgEquiv.ofAlgHom b i hbi hib

include hbound in
/-- ## 概要
有界 a 冪ねじれを持つ環 R の通常 a 進完備化は、元の標準 R 作用に関して a 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
実主イデアル完備化 H0 の完全忠実平坦性を、通常完備化との R 代数同型で移す。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
theorem isCompletelyFaithfullyFlat_adicCompletion_of_bounded_torsion :
    IsCompletelyFaithfullyFlat (Ideal.span {a}) (AdicCompletion (Ideal.span {a}) R) := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {a})
    (boundedPrincipalCompletionAdicAlgEquiv R a hbound).toLinearEquiv
    (principalCompletionH0_isCompletelyFaithfullyFlat R a hbound)
end SerrePositivity.BhattScholze.Andre.Transfinite
