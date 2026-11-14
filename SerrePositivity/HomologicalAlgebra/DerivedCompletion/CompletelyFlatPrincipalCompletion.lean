module
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Order.Notation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Basic.UnivLE
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons

public import SerrePositivity.CommutativeAlgebra.DirectLimit
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeScalar
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTor
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.CommutativeAlgebra.Adic.ReductionScalarExtension
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine

/-!
# 主完備化の完全忠実平坦性

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## 通常の忠実平坦性の環余極限による保存（旧 Andre/Transfinite/FaithfullyFlatColimit.lean）

BS 著者版 Theorem 7.14（著者版 p.61）の極限段の忠実性に使う一般論。
固定基底の代数の有向系を扱い、単位元を保つ遷移射であることを利用する。
-/

@[expose] public noncomputable section BoundedCompletion

open SerrePositivity SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (a : R) (n : ℕ) (b : R)
variable (hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
/-- ## 概要
有界 a 冪ねじれの下で、実際の導来完備化を既存の主イデアル完備化 H0 の離散対象と同定する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の完備化を補足する。

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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の完備化を補足する。

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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の完備化を補足する。

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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の完備化を補足する。

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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の完備化を補足する。

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


end SerrePositivity.BhattScholze.Andre.Transfinite

end BoundedCompletion

/-! ## 完全平坦・完全忠実平坦な環準同型の合成（旧 Andre/Transfinite/Composition.lean）

BS 著者版 Theorem 7.14（著者版 p.61）の超限塔で、各後続段から初期環までの性質を保つための一般論。
イデアルで消える任意の試験加群をスカラー拡大し、Tor と忠実性を二段階で検査する。
-/

