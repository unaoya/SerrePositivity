module
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.CommutativeAlgebra.Adic.ReductionScalarExtension
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Basic.UnivLE
public import Mathlib.Basic.Unique
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Defs

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# 正則元による剰余からの完全平坦性

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## André E1・E2：正則主剰余から二元完全平坦性を戻す（旧 Andre/Remark715/CompletelyFlatRegularReduction.lean）

## 概要

d が基底環と係数加群で正則なら、mod d の a 完全平坦性から元の (a,d) 完全平坦性が従う。
BS 著者版 Remark 7.15（著者版 p.62）の実候補の導来剰余を δ 完全化へ渡す一般計算。

## 方針

正則性で mod d の高次 Tor を消し、d で消える試験加群の Tor を底変換後に計算する。

## 規約

完備性・Noether 性・通常平坦性は要求しない。

## 使われ方

H/d の p 完全平坦性を実完備化 H の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section CompletelyFlatRegularReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

/-- 概要：正則主剰余の a 完全平坦性は元の (a,d) 完全平坦性を与える。
方針：d で消える試験加群に商作用を入れ、Tor 非輪状底変換で剰余の Tor 消滅を戻す。
規約：基底と係数加群の d 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全化前後の導来剰余比較。 -/
theorem completelyFlat_pair_of_regular_principal_reduction
    {R : Type u} [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (M : ModuleCat.{u} R) (hMd : IsSMulRegular M d)
    (hred : IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) a})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj M)) :
    IsCompletelyFlat (Ideal.span {a, d}) M := by
  let I : Ideal R := Ideal.span {d}
  let q := Ideal.Quotient.mk I
  let Mbar := (ModuleCat.extendScalars q).obj M
  have hTor := scalarExtensionTorVanishing_principal_of_regular d hd M hMd
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  have hId : I ≤ Ideal.span {a, d} := Ideal.span_mono (by simp)
  have ht : Module.IsTorsionBySet R N (I : Set R) :=
    fun {x} {r} => hN r (hId r.property) x
  let := ht.module
  let NQ := ModuleCat.of (R ⧸ I) N
  have hspan : Ideal.span {q a} ≤ Module.annihilator (R ⧸ I) N := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Module.mem_annihilator.mpr
    intro x
    change a • x = 0
    exact hN a (Ideal.subset_span (by simp)) x
  have hNa : ∀ r ∈ Ideal.span {q a}, ∀ x : N, r • x = 0 :=
    fun r hr x => Module.mem_annihilator.mp (hspan hr) x
  have : Subsingleton (TorModule (R ⧸ I) i Mbar N) :=
    (isConcentratedInDegreeZero_derivedTensor_iff Mbar N).mp (hred N hNa) i hi
  have : Subsingleton (TorModule (R ⧸ I) i N Mbar) :=
    (torModuleComm (R := R ⧸ I) i N Mbar).injective.subsingleton
  have hzQ' : IsZero (((Tor (ModuleCat (R ⧸ I)) i).obj NQ).obj Mbar) :=
    ModuleCat.isZero_of_subsingleton _
  have hz := ((ModuleCat.restrictScalars q).map_isZero hzQ').of_iso
    (torAcyclicBaseChangeIso q M hTor NQ i)
  let e : (ModuleCat.restrictScalars q).obj NQ ≃ₗ[R] N :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hz' : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R N)).obj M) :=
    hz.of_iso (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app M).symm
  have : Subsingleton (TorModule R i N M) := ModuleCat.subsingleton_of_isZero hz'
  have : Subsingleton (TorModule R i M N) := (torModuleComm (R := R) i M N).injective.subsingleton
  infer_instance

end SerrePositivity.BhattScholze.Andre

end CompletelyFlatRegularReduction

/-! ## André E1・E2：正則主環商から二元完全平坦性を戻す（旧 Andre/Remark715/CompletelyFlatRegularAlgebraReduction.lean）

## 概要

可換代数の正則主環商の完全平坦性を、元の係数作用に関する二元完全平坦性へ移す。
BS 著者版 Remark 7.15（著者版 p.62）の自然な実候補の導来剰余への接続。

## 方針

標準スカラー拡大と通常主環商の線形同型を作り、正則主剰余の一般判定を使う。

## 規約

基底環と代数での分母正則性を明示する。通常平坦性や Noether 性は不要。

## 使われ方

自然な Hodge–Tate 候補の p 完全平坦性を元の実完備化の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section CompletelyFlatRegularAlgebraReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
attribute [local instance] principalAdicQuotientAlgebra

/-- 概要：標準主剰余スカラー拡大は代数の通常主環商と剰余基底上線形同型。
方針：標準加群商への比較と通常主環商への比較を合成する。
規約：正則性を必要としない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な剰余作用の照合。 -/
def principalScalarExtensionAlgebraQuotientEquiv
    {R : Type u} [CommRing R] (d : R) (S : Type u) [CommRing S] [Algebra R S] :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj (ModuleCat.of R S)) ≃ₗ[
      R ⧸ Ideal.span {d}] (S ⧸ Ideal.span {algebraMap R S d}) :=
  (quotientScalarExtensionEquiv (Ideal.span {d}) (ModuleCat.of R S)).trans
    (principalAdicReductionEquiv d S)

/-- 概要：正則な主環商の a 完全平坦性は元の代数の (a,d) 完全平坦性を与える。
方針：通常主商を標準剰余スカラー拡大へ移して一般判定へ渡す。
規約：通常主商の係数作用は標準商代数構造。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の導来剰余の入力。 -/
theorem completelyFlat_pair_algebra_of_regular_reduction
    {R : Type u} [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S : Type u) [CommRing S] [Algebra R S] (hSd : IsSMulRegular S (algebraMap R S d))
    (hred : IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) a})
      (S ⧸ Ideal.span {algebraMap R S d})) :
    IsCompletelyFlat (Ideal.span {a, d}) S := by
  have hMd : IsSMulRegular (ModuleCat.of R S) d := by
    intro x y hxy
    apply hSd
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using hxy
  have hM := isCompletelyFlat_of_linearEquiv _
    (principalScalarExtensionAlgebraQuotientEquiv d S).symm hred
  exact completelyFlat_pair_of_regular_principal_reduction a d hd (ModuleCat.of R S) hMd hM

end SerrePositivity.BhattScholze.Andre

end CompletelyFlatRegularAlgebraReduction

/-! ## André E1・E2：二段の主剰余の忠実平坦性（旧 Andre/Remark715/CompletelyFaithfulPairReduction.lean）

## 概要

主剰余の完全忠実平坦性から元の二元剰余の忠実平坦性を得る。
BS 著者版 Remark 7.15（著者版 p.62）の導来剰余 H⁰ の準備。

## 方針

標準スカラー拡大を二段に分け、二重主商の係数同型に沿って忠実平坦性を底変換する。

## 規約

本工程では正則性を使わず、通常の剰余加群だけを扱う。

## 使われ方

自然な H/d の p 完全忠実平坦性から H の (p,d) 剰余の忠実平坦性へ進む。
-/

