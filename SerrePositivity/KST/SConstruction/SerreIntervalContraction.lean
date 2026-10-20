module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaps
public import SerrePositivity.DifferentialGraded.Complexes.UnitBoundary
public import SerrePositivity.DifferentialGraded.Complexes.DiskContractible

/-! # 元の鎖区間の一端点への収縮コチェイン
概要：max connection の辺の作用となる、元の一端点への次数 −1 の収縮を作る。
方針：単位からの元の辺と disk の収縮を合成し、微分を元の射の差として回収する。
規約：δ(s)=one∘augmentation−id。使われ方：区間から Hom(I,I) への lift と転置。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

private lemma unitMinusOne_boundary {A : Type u} [CommRing A] (K : Complex A)
    (e : K.X (-1)) (f g : 𝟙_ (Complex A) ⟶ K)
    (he : K.d (-1) 0 e = (cycleFromUnit K f).val - (cycleFromUnit K g).val) :
    δ (-1) 0 (unitMinusOne K e) = Cochain.ofHom f - Cochain.ofHom g := by
  apply Cochain.ext₀
  intro p
  by_cases hp : p = 0
  · subst p
    rw [Cochain.sub_v, Cochain.ofHom_v, Cochain.ofHom_v,
      δ_v (-1) 0 (by omega) (unitMinusOne K e) 0 0 (by omega) (-1) 1 rfl rfl]
    change (unitMinusOne K e).v 0 (-1) rfl ≫ K.d (-1) 0 +
      (0 : ℤ).negOnePow •
        ((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫
          (unitMinusOne K e).v 1 0 (by omega) = f.f 0 - g.f 0
    rw [single_obj_d, zero_comp, smul_zero, add_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change K.d (-1) 0 ((show A from a) • e) = f.f 0 a - g.f 0 a
    rw [map_smul, he, smul_sub]
    change (show A from a) • f.f 0 (1 : A) - (show A from a) • g.f 0 (1 : A) = _
    rw [← map_smul, ← map_smul]
    simp
  · exact (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) p hp).eq_of_src _ _

variable (A : Type u) [CommRing A]

/-- 元の鎖区間の増大写像は、零頂点の直和成分への射影。 -/
lemma serreIntervalAugmentation_eq_fst :
    serreIntervalAugmentation A = (biprod.fst : serreInterval A ⟶ 𝟙_ (Complex A)) := by
  have hz : (complexDiskHomEquiv A (𝟙_ (Complex A)) (-1)).symm 0 = 0 := by
    apply (complexDiskHomEquiv A (𝟙_ (Complex A)) (-1)).injective
    rw [Equiv.apply_symm_apply]
    rfl
  apply biprod.hom_ext'
  · simp only [serreIntervalAugmentation, serreIntervalLift, hz, biprod.inl_desc,
      biprod.inl_fst]
  · simp only [serreIntervalAugmentation, serreIntervalLift, hz, biprod.inr_desc,
      biprod.inr_fst]

/-- 元の零頂点への射影と disk の射影の和は、元の恒等射。 -/
lemma serreIntervalProjection_decomposition :
    serreIntervalAugmentation A ≫ serreIntervalZero A +
        (biprod.snd : serreInterval A ⟶ complexDisk A (-1)) ≫ biprod.inr = 𝟙 _ := by
  rw [serreIntervalAugmentation_eq_fst, serreIntervalZero]
  exact biprod.total

/-- 元の disk の収縮を、鎖区間の同じ直和成分へ延長する。 -/
def serreIntervalDiskContraction : Homogeneous (serreInterval A) (serreInterval A) (-1) :=
  ((Cochain.ofHom (biprod.snd : serreInterval A ⟶ complexDisk A (-1))).comp
    (complexDiskContractingCochain A (-1)) (zero_add (-1))).comp
      (Cochain.ofHom (biprod.inr : complexDisk A (-1) ⟶ serreInterval A)) (add_zero (-1))

/-- 延長した disk の収縮の微分は、元の disk 成分の射影。 -/
lemma serreIntervalDiskContraction_d :
    δ (-1) 0 (serreIntervalDiskContraction A) =
      Cochain.ofHom ((biprod.snd : serreInterval A ⟶ complexDisk A (-1)) ≫ biprod.inr) := by
  rw [serreIntervalDiskContraction, δ_comp_ofHom, δ_ofHom_comp, complexDiskContracting_d]
  simp only [Cochain.comp_id, ← Cochain.ofHom_comp]

/-- 元の一端点への収縮。辺を増大に沿って引き戻し、disk の収縮を引く。 -/
def serreIntervalContraction : Homogeneous (serreInterval A) (serreInterval A) (-1) :=
  (Cochain.ofHom (serreIntervalAugmentation A)).comp
    (unitMinusOne (serreInterval A) (serreIntervalEdge A)) (zero_add (-1)) -
      serreIntervalDiskContraction A

/-- 一端点への収縮の微分は、元の一端点への定数射から恒等射を引いたもの。 -/
lemma serreIntervalContraction_d :
    δ (-1) 0 (serreIntervalContraction A) =
      Cochain.ofHom (serreIntervalAugmentation A ≫ serreIntervalOne A) -
        Cochain.ofHom (𝟙 (serreInterval A)) := by
  rw [serreIntervalContraction, δ_sub, δ_ofHom_comp,
    unitMinusOne_boundary _ _ _ _ (serreIntervalEdge_d A), serreIntervalDiskContraction_d]
  simp only [Cochain.comp_sub, ← Cochain.ofHom_comp]
  have h := congrArg Cochain.ofHom (serreIntervalProjection_decomposition A)
  rw [Cochain.ofHom_add] at h
  rw [← h]
  abel

end SerrePositivity.KST.SConstruction
