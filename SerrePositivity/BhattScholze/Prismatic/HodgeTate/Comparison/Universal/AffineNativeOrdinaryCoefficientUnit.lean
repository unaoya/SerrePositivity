module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeCoefficientUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedCofaceCoefficientFactor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompleteSingleRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedCofaceCoefficientFactor
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompleteSingleRows

/-!
# 元の完備Tot係数比較の通常係数への分解

## 概要
元の完備Tot係数比較を、元の導来単位上で通常係数射と同じ終域単位へ分解する。

## 方針
有限列の長さを固定せず、二つの元の単位の等式を合成する。

## 規約
元の行の射も、元の標準Tot比較も保持する。

## 使われ方
HT04.R2の指定終域同型の単位上の値。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion
open HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 元のsingle行の通常係数射から得る、元の指定Tot係数射。 -/
def affineOrdinaryCofaceCoefficient
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ) :
    baseChange f.toRingHom (cosimplicialTotal (coefficientSingleRows (affineBaseModules P hP r))) ⟶
      cosimplicialTotal (coefficientSingleRows (affineBaseModules Q hQ r)) :=
  baseChangeTotalComparison f.toRingHom
      ((alternatingCofaceMapComplex (Complex A)).obj (coefficientSingleRows (affineBaseModules P hP r))) ≫
    (cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      ((alternatingCofaceFunctorIso ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ))).app
        (coefficientSingleRows (affineBaseModules P hP r))).hom ≫
    (alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      (affineAnyExtendedSingleRowsMap f hP hQ r)

/-- 元のsingle行での一般の完備化単位は、元の係数行の同じ単位である。 -/
private theorem cosimplicialFiniteCompletionUnit_singleRows {s : ℕ} (y : Fin s → B)
    (M : CosimplicialObject (ModuleCat.{u} B)) :
    cosimplicialFiniteCompletionUnit y (coefficientSingleRows M) =
      coefficientSingleFiniteCompletionUnit y M := rfl

/-- 元の導来単位上での、元の完備Tot係数射の通常係数による計算。 -/
theorem affineNativeCoefficient_unit_ordinary
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (r : ℕ) {s : ℕ} (x : Fin s → A) :
    let X := coefficientSingleRows (affineBaseModules P hP r)
    let Y := coefficientSingleRows (affineBaseModules Q hQ r)
    let y := fun j => f.toRingHom (x j)
    let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
    (finiteDerivedCompletionUnit y).app
      ((complexDerivedExtension f.toRingHom).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) ≫
      cosimplicialNativeCompletedBaseChangeComparison f.toRingHom x X 0
        (coefficientSingleRows_lowerBound (affineBaseModules P hP r)) ≫
      DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x)) =
    (complexDerivedExtensionAugmentation f.toRingHom).app (cosimplicialTotal X) ≫
      DerivedCategory.Q.map (affineOrdinaryCofaceCoefficient f hP hQ r) ≫
      DerivedCategory.Q.map (T.map (coefficientSingleFiniteCompletionUnit y (affineBaseModules Q hQ r))) := by
  let X := coefficientSingleRows (affineBaseModules P hP r)
  let Y := coefficientSingleRows (affineBaseModules Q hQ r)
  have hu := affineNativeCoefficient_unit f hP hQ r x
  have hf := baseChangeModelToCompletedCoefficientRows f.toRingHom x X Y
    (affineAnyExtendedSingleRowsMap f hP hQ r)
  have hq := congrArg DerivedCategory.Q.map hf
  have hfn := congrArg (fun k =>
    (complexDerivedExtensionAugmentation f.toRingHom).app (cosimplicialTotal X) ≫ k) hq
  simp only [Functor.map_comp, Category.assoc] at hfn
  dsimp only [X, Y, Functor.comp_map] at hu hfn
  have h := hu.trans hfn
  rw [cosimplicialFiniteCompletionUnit_singleRows] at h
  simpa only [affineOrdinaryCofaceCoefficient, Functor.comp_map, Functor.map_comp, Category.assoc] using h

/-- 元の終域単位が同型なら、元の完備Tot係数射の単位の式からその単位を外せる。 -/
theorem affineNativeCoefficient_cancel_unit
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (r : ℕ) {s : ℕ} (x : Fin s → A) :
    let X := coefficientSingleRows (affineBaseModules P hP r)
    let Y := coefficientSingleRows (affineBaseModules Q hQ r)
    let y := fun j => f.toRingHom (x j)
    let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
    let w := DerivedCategory.Q.map (T.map (coefficientSingleFiniteCompletionUnit y (affineBaseModules Q hQ r)))
    ∀ t : DerivedCategory.Q.obj (cosimplicialTotal (resolvedCompletedBaseChange f.toRingHom x X)) ⟶
        DerivedCategory.Q.obj (cosimplicialTotal Y),
      IsIso w → t ≫ w = DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x)) →
      (finiteDerivedCompletionUnit y).app
        ((complexDerivedExtension f.toRingHom).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) ≫
        cosimplicialNativeCompletedBaseChangeComparison f.toRingHom x X 0
          (coefficientSingleRows_lowerBound (affineBaseModules P hP r)) ≫ t =
      (complexDerivedExtensionAugmentation f.toRingHom).app (cosimplicialTotal X) ≫
        DerivedCategory.Q.map (affineOrdinaryCofaceCoefficient f hP hQ r) := by
  dsimp only
  intro t hw ht
  letI := hw
  apply (cancel_mono (DerivedCategory.Q.map
    ((alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      (coefficientSingleFiniteCompletionUnit (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r))))).mp
  simpa only [Category.assoc, ← ht] using affineNativeCoefficient_unit_ordinary f hP hQ r x

/-- 元の指定Tot同型は、終域の同じ標準単位と合成すると元のκのTotへ戻る。 -/
theorem affineResolvedCompletedTotalIso_unit
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (hg : Q.generator = (p : B)) (r : ℕ) {s : ℕ} (x : Fin s → A)
    (hTor : ∀ n, scalarExtensionTorVanishing f.toRingHom ((affineBaseModules P hP r).obj n))
    (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete B (f.toRingHom (x j))
      ((affineBaseModules Q hQ r).obj n)) :
    let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
    (affineResolvedCompletedTotalIso f hP hQ hg r x hTor hM).hom ≫
      DerivedCategory.Q.map (T.map (coefficientSingleFiniteCompletionUnit
        (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r))) =
    DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x)) := by
  let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
  let w := DerivedCategory.Q.map (T.map (coefficientSingleFiniteCompletionUnit
    (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r)))
  haveI : IsIso w := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    (coefficientSingleFiniteCompletionUnit_total_quasiIso
      (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r) hM)
  change (DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x)) ≫ inv w) ≫ w = _
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rfl

/-- 元の指定Tot同型の、元の導来単位上での通常係数による計算。 -/
theorem affineNativeTotalIso_unit
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (hg : Q.generator = (p : B)) (r : ℕ) {s : ℕ} (x : Fin s → A)
    (hTor : ∀ n, scalarExtensionTorVanishing f.toRingHom ((affineBaseModules P hP r).obj n))
    (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete B (f.toRingHom (x j))
      ((affineBaseModules Q hQ r).obj n)) :
    let X := coefficientSingleRows (affineBaseModules P hP r)
    (finiteDerivedCompletionUnit (fun j => f.toRingHom (x j))).app
      ((complexDerivedExtension f.toRingHom).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) ≫
      cosimplicialNativeCompletedBaseChangeComparison f.toRingHom x X 0
        (coefficientSingleRows_lowerBound (affineBaseModules P hP r)) ≫
      (affineResolvedCompletedTotalIso f hP hQ hg r x hTor hM).hom =
    (complexDerivedExtensionAugmentation f.toRingHom).app (cosimplicialTotal X) ≫
      DerivedCategory.Q.map (affineOrdinaryCofaceCoefficient f hP hQ r) := by
  have hw : IsIso (DerivedCategory.Q.map
      ((alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
        (coefficientSingleFiniteCompletionUnit (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r)))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (coefficientSingleFiniteCompletionUnit_total_quasiIso
        (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r) hM)
  exact affineNativeCoefficient_cancel_unit f hP hQ r x
    (affineResolvedCompletedTotalIso f hP hQ hg r x hTor hM).hom hw
    (affineResolvedCompletedTotalIso_unit f hP hQ hg r x hTor hM)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
