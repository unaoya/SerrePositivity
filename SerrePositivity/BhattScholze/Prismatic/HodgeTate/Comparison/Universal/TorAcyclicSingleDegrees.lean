module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicResolvedRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ComplexResolutionFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# 任意の元の次数のsingleへのTor非輪状な増大

## 概要
元の離散加群のTor消滅を、任意の指定次数のsingleへ置いた同じ増大へ移す。

## 方針
元のsingleとシフトの標準同型で零次へ戻し、係数拡大とシフトの標準自然同型を使う。

## 規約
元の複体自体のK-flat性を要求しない。増大のK-flat模型と元のTor消滅だけを使う。

## 使われ方
元のηの零次・一次形式のsingleの導来係数拡大。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 同じK-flat模型から任意の指定次数の元のsingleへの増大も、係数拡大で擬同型となる。 -/
theorem baseChange_quasiIso_to_singleDegree_of_torVanishing (f : A →+* B)
    (M : ModuleCat.{u} A) (hTor : scalarExtensionTorVanishing f M) (i : ℤ)
    {K : Complex A} (q : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj M)
    (hq : QuasiIso q) (hK : complexKFlat A K) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) := by
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
  let e := ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso i 0 i (by omega)).app M
  let q0 := q⟦i⟧' ≫ e.hom
  haveI := hq
  haveI : QuasiIso q0 := inferInstance
  have h0 := baseChange_quasiIso_to_single_of_torVanishing f M hTor q0 inferInstance
    (complexKFlat_shift A hK i)
  have hcomp : QuasiIso (E.map (q⟦i⟧') ≫ E.map e.hom) := by
    change QuasiIso (E.map (q⟦i⟧' ≫ e.hom)) at h0
    rw [E.map_comp] at h0
    exact h0
  have hshift : QuasiIso (E.map (q⟦i⟧')) :=
    (quasiIso_iff_comp_right _ _).mp hcomp
  have hcomm : QuasiIso ((E.map q)⟦i⟧') :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (((Functor.mapArrowFunctor _ _).mapIso (E.commShiftIso i)).app (Arrow.mk q))).mp hshift
  exact (CochainComplex.quasiIso_shift_iff (E.map q) i).mp hcomm

/-- 元のTor非輪状な加群の任意次数singleへの標準非有界導来増大は同型。 -/
theorem nativeDerivedAugmentation_singleDegree_isIso (f : A →+* B)
    (M : ModuleCat.{u} A) (hTor : scalarExtensionTorVanishing f M) (i : ℤ) :
    IsIso ((complexDerivedExtensionAugmentation f).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj M)) := by
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj M
  let q := (complexResolutionAugmentation A).app K
  haveI := complexResolutionAugmentation_quasiIso A K
  haveI := baseChange_quasiIso_to_singleDegree_of_torVanishing f M hTor i q inferInstance
    (complexResolutionFunctor_kFlat A K)
  haveI := complexDerivedExtensionAugmentation_isIso f _ (complexResolutionFunctor_kFlat A K)
  have hn := (complexDerivedExtensionAugmentation f).naturality q
  haveI : IsIso ((complexDerivedExtension f).map (DerivedCategory.Q.map q) ≫
      (complexDerivedExtensionAugmentation f).app K) := by
    change (complexDerivedExtension f).map (DerivedCategory.Q.map q) ≫
      (complexDerivedExtensionAugmentation f).app K =
      (complexDerivedExtensionAugmentation f).app ((complexResolutionFunctor A).obj K) ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) at hn
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((complexDerivedExtension f).map (DerivedCategory.Q.map q)) _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
