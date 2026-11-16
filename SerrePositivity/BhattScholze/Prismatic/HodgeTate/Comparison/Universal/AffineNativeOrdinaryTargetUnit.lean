module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryCofaceCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NativeCompletedModelUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AssociatedCompletionComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryCoefficientUnit

/-!
# 元の完備Tot終域比較の単位の式

## 概要
同じ元の指定比較を、反復完備化の長さを固定する前に通常係数へ戻す。

## 方針
座標の比較・元の導来模型・元のTot同型の単位の式を順に合成する。

## 規約
Tot同型や終域の同型を新しく定義し直さない。

## 使われ方
HT04.R2で具体的な被覆に代入する前の、元の射の照合。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 元の指定比較の合成は、同じ通常係数比較と元の増大を計算する。 -/
theorem affineNativeOrdinaryTarget_unit
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (hg : Q.generator = (p : B)) (r : ℕ) {s : ℕ} (x : Fin s → A) (z : Fin s → B)
    (hcoords : ∀ j, Associated (f.toRingHom (x j)) (z j))
    (hTor : ∀ n, scalarExtensionTorVanishing f.toRingHom ((affineBaseModules P hP r).obj n))
    (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete B (f.toRingHom (x j))
      ((affineBaseModules Q hQ r).obj n)) :
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let D := complexDerivedExtension f.toRingHom
  let y := fun j => f.toRingHom (x j)
  let F := finiteDerivedCompletionFunctor y
  let U := finiteDerivedCompletionUnit y
  let K := affineComplexOnBase P r (affineHTTotalComplex P hP r)
  let S := (complexResolutionFunctor A).obj K
  let q : S ⟶ K := (complexResolutionAugmentation A).app K
  let X := affineBaseSingleRows P hP r
  let Z := cosimplicialTotal X
  let eP := affineBaseSingleTotalPolynomialIso P hP r
  let eQ := affineBaseSingleTotalPolynomialIso Q hQ r
  let n := nativeCompletedScalarModelIso f.toRingHom x q
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  let nd := nativeDerivedScalarModelIso f.toRingHom q
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  let c := associatedFiniteCompletionIso y z hcoords (E.obj S)
  let v := cosimplicialNativeCompletedBaseChangeComparison f.toRingHom x
    X 0 (affineBaseSingleRows_lowerBound P hP r)
  let t := affineResolvedCompletedTotalIso f hP hQ hg r x hTor hM
  let o := affineAnyOrdinaryTotalIso f hP hQ hg r
  let a := complexDerivedExtensionAugmentation f.toRingHom
  DerivedCategory.Q.map (finiteCompletionUnit z (E.obj S)) ≫ c.inv ≫ n.inv ≫
    F.map (D.map (DerivedCategory.Q.map eP.inv)) ≫ v ≫ t.hom ≫ DerivedCategory.Q.map eQ.hom =
    DerivedCategory.Q.map (E.map q) ≫ DerivedCategory.Q.map o.hom := by
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let D := complexDerivedExtension f.toRingHom
  let y := fun j => f.toRingHom (x j)
  let F := finiteDerivedCompletionFunctor y
  let U := finiteDerivedCompletionUnit y
  let K := affineComplexOnBase P r (affineHTTotalComplex P hP r)
  let S := (complexResolutionFunctor A).obj K
  let q : S ⟶ K := (complexResolutionAugmentation A).app K
  let X := affineBaseSingleRows P hP r
  let Z := cosimplicialTotal X
  let eP := affineBaseSingleTotalPolynomialIso P hP r
  let eQ := affineBaseSingleTotalPolynomialIso Q hQ r
  let n := nativeCompletedScalarModelIso f.toRingHom x q
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  let nd := nativeDerivedScalarModelIso f.toRingHom q
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  let c := associatedFiniteCompletionIso y z hcoords (E.obj S)
  let v := cosimplicialNativeCompletedBaseChangeComparison f.toRingHom x
    X 0 (affineBaseSingleRows_lowerBound P hP r)
  let t := affineResolvedCompletedTotalIso f hP hQ hg r x hTor hM
  let o := affineAnyOrdinaryTotalIso f hP hQ hg r
  let a := complexDerivedExtensionAugmentation f.toRingHom
  have hc : DerivedCategory.Q.map (finiteCompletionUnit z (E.obj S)) ≫ c.inv =
      DerivedCategory.Q.map (finiteCompletionUnit y (E.obj S)) := by
    apply (cancel_mono c.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (associatedFiniteCompletionIso_unit y z hcoords (E.obj S)).symm
  have hn : DerivedCategory.Q.map (finiteCompletionUnit y (E.obj S)) ≫ n.inv =
      nd.inv ≫ U.app (D.obj (DerivedCategory.Q.obj K)) :=
    nativeCompletedScalarModelIso_unit f.toRingHom x q
      (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  have hu := U.naturality (D.map (DerivedCategory.Q.map eP.inv))
  simp only [Functor.id_map] at hu
  have ht : U.app (D.obj (DerivedCategory.Q.obj Z)) ≫ v ≫ t.hom =
      a.app Z ≫ DerivedCategory.Q.map (affineOrdinaryCofaceCoefficient f hP hQ r) := by
    simpa only [affineBaseSingleRows] using
      affineNativeTotalIso_unit f hP hQ hg r x hTor hM
  have ha : D.map (DerivedCategory.Q.map eP.inv) ≫ a.app Z =
      a.app K ≫ DerivedCategory.Q.map (E.map eP.inv) := a.naturality eP.inv
  have hnd : nd.inv ≫ a.app K = DerivedCategory.Q.map (E.map q) := by
    apply (cancel_epi nd.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      (HTComparisonTotal.nativeDerivedScalarModelIso_comp_augmentation f.toRingHom q
        (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)).symm
  have hco := congrArg DerivedCategory.Q.map (affineOrdinaryCofaceCoefficient_compatibility f hP hQ hg r)
  simp only [Functor.map_comp] at hco
  change DerivedCategory.Q.map (finiteCompletionUnit z (E.obj S)) ≫ c.inv ≫ n.inv ≫
    F.map (D.map (DerivedCategory.Q.map eP.inv)) ≫ v ≫ t.hom ≫ DerivedCategory.Q.map eQ.hom =
    DerivedCategory.Q.map (E.map q) ≫ DerivedCategory.Q.map o.hom
  rw [reassoc_of% hc, reassoc_of% hn, ← reassoc_of% hu, reassoc_of% ht,
    reassoc_of% ha, reassoc_of% hnd, hco]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
