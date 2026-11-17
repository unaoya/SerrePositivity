module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedScalarModels
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension

/-!
# 本体の非有界導来係数拡大と指定 K-flat 模型

## 概要
本体の complexDerivedExtension の同じ標準増大により、任意の指定 K-flat 分解で計算する。

## 方針
分解の擬同型を本体の導来関手で写し、K-flat 入力での標準増大の同型を使う。

## 規約
入力自体の K-flat 性は要求しない。元の標準増大と模型の実際の射を保つ。

## 使われ方
BS 著者版 Lemma 4.22 の S 線形の標準導来底変換との同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.DifferentialGraded.ScalarExtension

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 任意の非有界入力の、本体の標準導来係数拡大の指定模型による計算。 -/
def nativeDerivedScalarModelIso (f : R →+* S) {P K : Complex R}
    (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (complexDerivedExtension f).obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj (baseChange f P) := by
  haveI := hq
  exact (asIso ((complexDerivedExtension f).map (DerivedCategory.Q.map q))).symm ≪≫
    complexDerivedExtensionKFlatIso f P hP

/-- 分解の擬同型との合成で、元の K-flat 入力での標準増大に戻る。 -/
@[reassoc] theorem derived_map_comp_nativeDerivedScalarModelIso (f : R →+* S)
    {P K : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    (complexDerivedExtension f).map (DerivedCategory.Q.map q) ≫
        (nativeDerivedScalarModelIso f q hq hP).hom = (complexDerivedExtensionKFlatIso f P hP).hom := by
  haveI := hq
  simp only [nativeDerivedScalarModelIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]

/-- 指定模型の実際の可換な射を、同じ標準導来底変換の射へ渡す。 -/
@[reassoc] theorem nativeDerivedScalarModelIso_naturality (f : R →+* S)
    {P Q K M : Complex R} (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P)
    (q' : Q ⟶ M) (hq' : QuasiIso q') (hQ : complexKFlat R Q)
    (g : K ⟶ M) (h : P ⟶ Q) (comm : q ≫ g = h ≫ q') :
    (complexDerivedExtension f).map (DerivedCategory.Q.map g) ≫ (nativeDerivedScalarModelIso f q' hq' hQ).hom =
      (nativeDerivedScalarModelIso f q hq hP).hom ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h) := by
  haveI := hq
  apply (cancel_epi ((complexDerivedExtension f).map (DerivedCategory.Q.map q))).mp
  have hc := congrArg (fun t => (complexDerivedExtension f).map (DerivedCategory.Q.map t)) comm
  simp only [Functor.map_comp] at hc
  calc
    _ = (complexDerivedExtension f).map (DerivedCategory.Q.map h) ≫
        ((complexDerivedExtension f).map (DerivedCategory.Q.map q') ≫ (nativeDerivedScalarModelIso f q' hq' hQ).hom) := by
      rw [← Category.assoc, hc, Category.assoc]
    _ = (complexDerivedExtension f).map (DerivedCategory.Q.map h) ≫ (complexDerivedExtensionKFlatIso f Q hQ).hom := by
      rw [derived_map_comp_nativeDerivedScalarModelIso]
    _ = (complexDerivedExtensionKFlatIso f P hP).hom ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h) :=
      complexDerivedExtensionKFlatIso_naturality f hP hQ h
    _ = _ := by rw [← Category.assoc, derived_map_comp_nativeDerivedScalarModelIso]

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 固定 R 係数模型は、本体の標準 S 導来底変換を係数制限した模型である。 -/
def nativeDerivedRestrictionIso {P K : Complex R}
    (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    DerivedCategory.Q.obj (L.tensorFunctor.obj K) ≅
      (derivedRestrictScalars f).obj ((complexDerivedExtension f).obj (DerivedCategory.Q.obj K)) :=
  L.baseChangeModelIso q hq hP ≪≫ (derivedRestrictScalars f).mapIso (nativeDerivedScalarModelIso f q hq hP).symm

/-- 同じ標準 S 導来底変換の完備化への、指定模型上の計算同型。 -/
def finiteNativeDerivedRestrictionIso {r : ℕ} (x : Fin r → R) {P K : Complex R}
    (q : P ⟶ K) (hq : QuasiIso q) (hP : complexKFlat R P) :
    DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj (L.tensorFunctor.obj K)) ≅
      (derivedRestrictScalars f).obj ((finiteDerivedCompletionFunctor (fun j => f (x j))).obj
        ((complexDerivedExtension f).obj (DerivedCategory.Q.obj K))) :=
  L.finiteCompletedBaseChangeModelIso x q hq hP ≪≫ (derivedRestrictScalars f).mapIso
    ((finiteDerivedCompletionFunctor (fun j => f (x j))).mapIso (nativeDerivedScalarModelIso f q hq hP).symm)

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
