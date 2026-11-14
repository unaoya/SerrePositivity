module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Basic.Unique
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic

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
# 完全平坦性と完全忠実平坦性の合成

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## 通常の忠実平坦性の環余極限による保存（旧 Andre/Transfinite/FaithfullyFlatColimit.lean）

BS 著者版 Theorem 7.14（著者版 p.61）の極限段の忠実性に使う一般論。
固定基底の代数の有向系を扱い、単位元を保つ遷移射であることを利用する。
-/

@[expose] public noncomputable section Composition

namespace SerrePositivity.BhattScholze.Andre.Transfinite
open SerrePositivity CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- ## 概要
スカラー制限で記述した二つの完全平坦写像の合成は完全平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の塔の後続段に用いる補助命題。

## 方針
試験加群の Tor 非輪状性から実際の底変換 Tor 比較を適用し、拡大後の試験加群には
拡張イデアルが零として作用することを使う。

## 規約
元の合成環準同型の作用と、二段階のスカラー制限の作用を線形同型で明示的に比較する。

## 使われ方
toAlgebra を使う公開版の証明に使う。
-/
private theorem completelyFlat_comp_restricted {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (I : Ideal R)
    (hB : IsCompletelyFlat I (baseChangeScalarModule φ))
    (hC : IsCompletelyFlat (I.map φ) (baseChangeScalarModule ψ)) :
    IsCompletelyFlat I (baseChangeScalarModule (ψ.comp φ)) := by
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff _ N).mpr
  intro i hi
  let N' := ModuleCat.of R N
  have hTor : scalarExtensionTorVanishing φ N' := hB N hN
  let M := (ModuleCat.extendScalars φ).obj N'
  have hAnn : I.map φ ≤ Module.annihilator B M := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    exact Module.mem_annihilator.mpr (scalarExtension_annihilated φ r N' (hN r hr))
  have hMI : ∀ r ∈ I.map φ, ∀ x : M, r • x = 0 :=
    fun r hr x ↦ Module.mem_annihilator.mp (hAnn hr) x
  have hz := hC M hMI i hi
  have hz' : IsZero (((Tor (ModuleCat B) i).obj (baseChangeScalarModule ψ)).obj M) := hz
  have hzR := (ModuleCat.restrictScalars φ).map_isZero hz'
  have he := torAcyclicBaseChangeIso φ N' hTor (baseChangeScalarModule ψ) i
  have hzOriginal := hzR.of_iso he
  let E : (baseChangeScalarModule (ψ.comp φ)) ≃ₗ[R]
      ((ModuleCat.restrictScalars φ).obj (baseChangeScalarModule ψ)) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hzFinal := hzOriginal.of_iso (((Tor (ModuleCat R) i).mapIso E.toModuleIso).app N')
  exact ModuleCat.subsingleton_of_isZero hzFinal

/-- ## 概要
I 完全平坦な R → B と IB 完全平坦な B → C の合成は I 完全平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の超限塔の後続段で使用する。

## 方針
試験加群の底変換と Tor 比較による補助命題を、元の環準同型の toAlgebra 作用で適用する。

## 規約
p 正則性・完備性・有限生成性を要求しない。拡張イデアルは I.map φ。

## 使われ方
各段から初期環への完全平坦性を、後続段へ合成して運ぶ。
-/
theorem isCompletelyFlat_comp {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (I : Ideal R)
    (hB : letI := φ.toAlgebra; IsCompletelyFlat I B)
    (hC : letI := ψ.toAlgebra; IsCompletelyFlat (I.map φ) C) :
    letI := (ψ.comp φ).toAlgebra; IsCompletelyFlat I C := by
  exact completelyFlat_comp_restricted φ ψ I hB hC

/-- ## 概要
通常剰余テンソルが忠実平坦なら、I で消える試験加群の零性は元のテンソルで検出できる。
BS 著者版 Theorem 7.14（著者版 p.61）の合成の忠実性に用いる一般補題。

## 方針
試験加群に R/I 作用を与え、通常テンソルの底変換消去同型を通して忠実平坦性を適用する。

## 規約
P 自身の完全平坦性や通常平坦性は不要。N は I の元すべてで消える。

## 使われ方
二段の拡大後に試験加群が零になれば、順に元へ戻して零性を検出する。
-/
theorem subsingleton_of_annihilated_of_residueTensor {R : Type u} [CommRing R] (I : Ideal R)
    (P : Type u) [AddCommGroup P] [Module R P]
    (hP : Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] P))
    (N : Type u) [AddCommGroup N] [Module R N]
    (hN : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hTensor : Subsingleton (N ⊗[R] P)) : Subsingleton N := by
  let hNt : Module.IsTorsionBySet R N (I : Set R) := fun {x} {r} ↦ hN r r.property x
  let := hNt.module
  have : IsScalarTower R (R ⧸ I) N := inferInstance
  let := hP
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N P
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] P)) := e.injective.subsingleton
  exact Module.FaithfullyFlat.rTensor_reflects_triviality (R ⧸ I) ((R ⧸ I) ⊗[R] P) N

/-- ## 概要
I 完全忠実平坦な R → B と IB 完全忠実平坦な B → C の合成は I 完全忠実平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の塔の後続段で使う。

## 方針
完全平坦性を Tor の底変換で合成し、通常剰余テンソルの平坦性を得る。
忠実性は I で消える試験加群を二段階の忠実なテンソルで反映して証明する。

## 規約
I は任意。非零性・p 正則性・通常平坦性・完備性は不要。
環の作用はすべて指定した環準同型の toAlgebra。

## 使われ方
初期環から各段への p 完全忠実平坦性を、後続写像との合成で保つ。
-/
theorem isCompletelyFaithfullyFlat_comp {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (I : Ideal R)
    (hB : letI := φ.toAlgebra; IsCompletelyFaithfullyFlat I B)
    (hC : letI := ψ.toAlgebra; IsCompletelyFaithfullyFlat (I.map φ) C) :
    letI := (ψ.comp φ).toAlgebra; IsCompletelyFaithfullyFlat I C := by
  let := φ.toAlgebra
  let := ψ.toAlgebra
  let := (ψ.comp φ).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  have hFlat : IsCompletelyFlat I C := completelyFlat_comp_restricted φ ψ I hB.1 hC.1
  refine ⟨hFlat, ?_⟩
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality (R ⧸ I) _).mpr
  refine ⟨flat_residueTensor_of_completelyFlat I C hFlat, ?_⟩
  intro N _ _ hTensor
  let _ : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  have : IsScalarTower R (R ⧸ I) N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e0 := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N C
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] C)) := hTensor
  have hNC : Subsingleton (N ⊗[R] C) := e0.symm.injective.subsingleton
  have : Subsingleton (C ⊗[R] N) := (TensorProduct.comm R C N).injective.subsingleton
  let M := B ⊗[R] N
  let e1 := (TensorProduct.comm B M C).trans
    (AlgebraTensorModule.cancelBaseChange R B B C N)
  have hMC : Subsingleton (M ⊗[B] C) := e1.injective.subsingleton
  have hNI : ∀ r ∈ I, ∀ x : N, r • x = 0 := by
    intro r hr x
    change Ideal.Quotient.mk I r • x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  have hAnn : I.map φ ≤ Module.annihilator B M := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    apply Module.mem_annihilator.mpr
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      change (r • b) ⊗ₜ[R] n = 0
      rw [TensorProduct.smul_tmul, hNI r hr, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, zero_add]
  have hM : Subsingleton M := subsingleton_of_annihilated_of_residueTensor (I.map φ) C hC.2 M
    (fun r hr x ↦ Module.mem_annihilator.mp (hAnn hr) x) hMC
  have hNB : Subsingleton (N ⊗[R] B) := (TensorProduct.comm R N B).injective.subsingleton
  exact subsingleton_of_annihilated_of_residueTensor I B hB.2 N hNI hNB

end SerrePositivity.BhattScholze.Andre.Transfinite

end Composition

/-! ## 完全平坦性の余極限による保存（旧 Andre/Transfinite/CompleteFlatColimit.lean）

BS 著者版 Theorem 7.14（著者版 p.61）の極限段に使う、固定基底上の完全平坦性の保存。
Tor の対称性と正確な余極限との交換を使い、通常平坦性への置き換えは行わない。
忠実性は別の環論的課題として扱う。
-/

