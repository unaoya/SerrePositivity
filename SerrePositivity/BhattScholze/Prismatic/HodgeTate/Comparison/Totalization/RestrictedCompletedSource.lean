module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RestrictedCompletedRows

/-!
# 元の S 完備底変換の指定 R 計算模型

## 概要
K-flat 入力の同じ係数増大と S 標準単位の合成から、完備源の計算同型を作る。

## 方針
実際の二本の擬同型を使う。同型と元の R 標準単位の合成を正規化する。

## 規約
S 完備化の単位を任意の同型で置き換えない。

## 使われ方
BS 著者版 Lemma 4.22 の標準 S 線形比較の源。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]
namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 同じ係数増大と S 標準単位からなる実際の源の射。 -/
def toRestrictedCompletedSource {r : ℕ} (x : Fin r → R) (P : Complex R) :
    L.tensorFunctor.obj P ⟶
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        ((finiteCompletionFunctor (fun j => f (x j))).obj (baseChange f P))) :=
  L.comparison P ≫ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
    (finiteCompletionUnit (fun j => f (x j)) (baseChange f P))

/-- K-flat 入力では、同じ源の射は R 再完備化によって擬同型となる。 -/
theorem completedToRestrictedSource_quasiIso {r : ℕ} (x : Fin r → R)
    (P : Complex R) (hP : complexKFlat R P) :
    QuasiIso ((finiteCompletionFunctor x).map (L.toRestrictedCompletedSource x P)) := by
  dsimp only [toRestrictedCompletedSource]
  rw [Functor.map_comp]
  haveI := L.comparison_quasiIso P hP
  haveI := finiteCompletionFunctor_map_quasiIso x (L.comparison P)
  haveI := restricted_finiteCompletionUnit_completion_quasiIso f x (baseChange f P)
  infer_instance

/-- 二本の元の射で指定した、制限された S 完備源の計算同型。 -/
def restrictedCompletedSourceIso {r : ℕ} (x : Fin r → R) (P : Complex R)
    (hP : complexKFlat R P) :
    DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj (L.tensorFunctor.obj P)) ≅
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        ((finiteCompletionFunctor (fun j => f (x j))).obj (baseChange f P))) := by
  haveI := L.completedToRestrictedSource_quasiIso x P hP
  haveI := finiteCompletionUnit_isIso_of_isComplete x _
    (restricted_finiteCompletion_isComplete f x (baseChange f P))
  exact asIso (DerivedCategory.Q.map ((finiteCompletionFunctor x).map
      (L.toRestrictedCompletedSource x P))) ≪≫
    (asIso (DerivedCategory.Q.map (finiteCompletionUnit x _))).symm

/-- 計算同型は元の R 標準単位を、元の係数増大と S 標準単位の合成へ写す。 -/
@[reassoc] theorem unit_comp_restrictedCompletedSourceIso {r : ℕ} (x : Fin r → R)
    (P : Complex R) (hP : complexKFlat R P) :
    DerivedCategory.Q.map (finiteCompletionUnit x (L.tensorFunctor.obj P)) ≫
      (L.restrictedCompletedSourceIso x P hP).hom =
        DerivedCategory.Q.map (L.toRestrictedCompletedSource x P) := by
  haveI := L.completedToRestrictedSource_quasiIso x P hP
  haveI := finiteCompletionUnit_isIso_of_isComplete x _
    (restricted_finiteCompletion_isComplete f x (baseChange f P))
  have h := congrArg DerivedCategory.Q.map
    (finiteCompletionUnit_naturality x (L.toRestrictedCompletedSource x P))
  simp only [Functor.map_comp] at h
  dsimp only [restrictedCompletedSourceIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
