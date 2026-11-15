module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExtension
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExtension

/-!
# affine 項の元の完備係数変更の同型判定

## 概要
通常の係数変更が指定された代数同型を計算するとき、既存の標準完備係数変更も同型になる。

## 方針
元の通常の延長を同じ代数同型で読み、完備な標的の完備化単位を戻す。

## 規約
標的の導来 p 完備性と、純テンソル上で元の射を計算する式を明示する。

## 使われ方
結晶的な affine 剰余行の環比較を、元の標準完備係数変更へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable (p : ℕ) (k l A B : Type u) [CommRing k] [CommRing l] [CommRing A] [CommRing B]
variable [Algebra k l] [Algebra k A] [Algebra l B] [Algebra k B] [IsScalarTower k l B]
variable (hc : IsModuleComplete l (p : l) (ModuleCat.of l B)) (f : A →ₐ[k] B)

/-- 指定された通常の代数比較が同型なら、同じ元の完備係数比較も同型。 -/
theorem affinePointwiseCompletedAlgMap_isIso
    (e : l ⊗[k] A ≃ₐ[l] B) (he : ∀ x : A, e ((1 : l) ⊗ₜ[k] x) = f x) :
    IsIso (pointwiseCompletedAlgMap p k l A B hc f) := by
  have heq : AlgHom.liftEquiv k l A B f = e.toAlgHom := by
    apply (AlgHom.liftEquiv k l A B).symm.injective
    rw [Equiv.symm_apply_apply]
    apply AlgHom.ext
    intro x
    exact (he x).symm
  haveI : IsIso (ModuleCat.ofHom (AlgHom.liftEquiv k l A B f).toLinearMap) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    rw [heq]
    exact e.bijective
  haveI : IsIso (ordinaryExtension k l A B f) := by
    dsimp only [ordinaryExtension]
    infer_instance
  haveI : IsIso ((moduleCompletionH0Unit l (p : l)).app (ModuleCat.of l B)) :=
    moduleCompletionH0Unit_isIso_of_complete l (p : l) (ModuleCat.of l B) hc
  let E := (moduleCompletionH0Functor l (p : l)).mapIso
    (asIso (ordinaryExtension k l A B f))
  let U := asIso ((moduleCompletionH0Unit l (p : l)).app (ModuleCat.of l B))
  change IsIso (E.hom ≫ U.inv)
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
