module
public import SerrePositivity.DifferentialGraded.Complexes.DiskGenerator
public import SerrePositivity.DifferentialGraded.Complexes.UnitTensor
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Serre 対角に使う元の鎖区間
概要：二つの閉頂点と、その差を微分に持つ辺からなる鎖区間を構成する。
方針：単位複体と次数 −1 の disk の直和を使い、元の生成元で射を判定する。
規約：d(edge)=one−zero。使われ方：cubical Serre 対角と dg nerve の tensor 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖区間。零頂点と、辺からその境界への disk の直和。 -/
abbrev serreInterval : Complex A := 𝟙_ (Complex A) ⊞ complexDisk A (-1)

/-- 鎖区間の元の零頂点。 -/
def serreIntervalZero : 𝟙_ (Complex A) ⟶ serreInterval A := biprod.inl

/-- 鎖区間の元の辺。 -/
def serreIntervalEdge : (serreInterval A).X (-1) :=
  complexDiskHomEquiv A (serreInterval A) (-1) biprod.inr

/-- 鎖区間の元の辺の閉境界。 -/
def serreIntervalBoundary : 𝟙_ (Complex A) ⟶ serreInterval A :=
  complexSphereToDisk A (-1) ≫ (biprod.inr : complexDisk A (-1) ⟶ serreInterval A)

/-- 鎖区間の元の一頂点。零頂点に辺の境界を加える。 -/
def serreIntervalOne : 𝟙_ (Complex A) ⟶ serreInterval A :=
  serreIntervalZero A + serreIntervalBoundary A

/-- 元の鎖区間からの射は、零頂点と辺の像で一意に決まる。 -/
lemma serreInterval_hom_ext {K : Complex A} {f g : serreInterval A ⟶ K}
    (h₀ : serreIntervalZero A ≫ f = serreIntervalZero A ≫ g)
    (he : f.f (-1) (serreIntervalEdge A) = g.f (-1) (serreIntervalEdge A)) : f = g := by
  apply biprod.hom_ext' f g h₀
  apply (complexDiskHomEquiv A K (-1)).injective
  simpa only [serreIntervalEdge, complexDiskHomEquiv_naturality] using he

/-- 零頂点の像と辺の像から元の鎖区間の chain map を作る。 -/
def serreIntervalLift {K : Complex A} (z : 𝟙_ (Complex A) ⟶ K) (e : K.X (-1)) :
    serreInterval A ⟶ K :=
  biprod.desc z ((complexDiskHomEquiv A K (-1)).symm e)

/-- 元の零頂点は、指定した閉零射を厳密に回収する。 -/
lemma serreIntervalLift_zero {K : Complex A} (z : 𝟙_ (Complex A) ⟶ K) (e : K.X (-1)) :
    serreIntervalZero A ≫ serreIntervalLift A z e = z := by
  exact biprod.inl_desc _ _

/-- 元の辺は、指定した次数 −1 の元を厳密に回収する。 -/
lemma serreIntervalLift_edge {K : Complex A} (z : 𝟙_ (Complex A) ⟶ K) (e : K.X (-1)) :
    (serreIntervalLift A z e).f (-1) (serreIntervalEdge A) = e := by
  have h := congrArg (complexDiskHomEquiv A K (-1))
    (biprod.inr_desc z ((complexDiskHomEquiv A K (-1)).symm e))
  rw [complexDiskHomEquiv_naturality, Equiv.apply_symm_apply] at h
  exact h

/-- 元の辺の微分は、元の一頂点と零頂点の差。 -/
lemma serreIntervalEdge_d :
    (serreInterval A).d (-1) 0 (serreIntervalEdge A) =
      (cycleFromUnit _ (serreIntervalOne A)).val -
        (cycleFromUnit _ (serreIntervalZero A)).val := by
  have h := complexSphereToDisk_comp A (-1)
    (biprod.inr : complexDisk A (-1) ⟶ serreInterval A)
  change (cycleFromUnit _ (complexSphereToDisk A (-1) ≫ biprod.inr)).val =
    (serreInterval A).d (-1) 0 (serreIntervalEdge A) at h
  rw [← h]
  change _ = (serreIntervalZero A + serreIntervalBoundary A).f 0
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) - _
  change (cycleFromUnit _ (serreIntervalBoundary A)).val =
    ((cycleFromUnit _ (serreIntervalZero A)).val +
      (cycleFromUnit _ (serreIntervalBoundary A)).val) -
      (cycleFromUnit _ (serreIntervalZero A)).val
  exact (add_sub_cancel_left _ _).symm

end SerrePositivity.KST.SConstruction
