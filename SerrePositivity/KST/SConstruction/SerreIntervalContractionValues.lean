module
public import SerrePositivity.KST.SConstruction.SerreIntervalMax
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 元の区間の収縮の端点・辺での値
概要：一端点への収縮が、零端点を元の辺、一端点と辺を零に写すことを示す。
方針：同じ直和射影と disk の上下の生成元で評価する。
規約：単位と disk の元の生成元を保持する。使われ方：max connection の右端点則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

private lemma boundaryCycle {A : Type u} [CommRing A] (n : ℤ) :
    (complexSphereHomEquiv A (complexDisk A n) (n + 1)
      (complexSphereToDisk A n)).val = (complexDiskX₁ A n).inv (1 : A) := by
  have h := complexSphereToDisk_comp A n (𝟙 (complexDisk A n))
  rw [Category.comp_id] at h
  exact h.trans (complexDisk_upper_apply A n (𝟙 (complexDisk A n))).symm

private lemma diskContraction_upper {A : Type u} [CommRing A] (n : ℤ) :
    (complexDiskContractingCochain A n).v (n + 1) n (by omega)
        ((complexDiskX₁ A n).inv (1 : A)) = (complexDiskX₀ A n).inv (1 : A) := by
  rw [complexDiskContractingCochain, Cochain.single_v]
  change (((complexDiskX₁ A n).inv ≫ (complexDiskX₁ A n).hom) ≫
    (complexDiskX₀ A n).inv) (1 : A) = _
  rw [Iso.inv_hom_id, Category.id_comp]

private lemma unitMinusOne_generator {A : Type u} [CommRing A] (K : Complex A)
    (e : K.X (-1)) :
    (unitMinusOne K e).v 0 (-1) (by omega)
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = e := by
  change (1 : A) • e = e
  exact one_smul A e

variable (A : Type u) [CommRing A]

/-- 元の零端点の disk 成分は零。 -/
lemma serreIntervalZero_snd_value :
    (biprod.snd : serreInterval A ⟶ complexDisk A (-1)).f 0
        (cycleFromUnit _ (serreIntervalZero A)).val = 0 :=
  congrArg (fun f => f.f 0 (1 : A))
    (biprod.inl_snd (X := 𝟙_ (Complex A)) (Y := complexDisk A (-1)))

/-- 元の一端点の disk 成分は、元の辺の閉境界。 -/
lemma serreIntervalOne_snd :
    serreIntervalOne A ≫ (biprod.snd : serreInterval A ⟶ complexDisk A (-1)) =
      serreIntervalBoundary A ≫ biprod.snd := by
  simp only [serreIntervalOne, serreIntervalZero, Preadditive.add_comp,
    biprod.inl_snd, zero_add]

/-- 元の一端点の disk 成分は、その上の元の生成元。 -/
lemma serreIntervalOne_snd_value :
    (biprod.snd : serreInterval A ⟶ complexDisk A (-1)).f 0
        (cycleFromUnit _ (serreIntervalOne A)).val = (complexDiskX₁ A (-1)).inv (1 : A) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalOne_snd A)
  dsimp only [serreIntervalBoundary] at h
  rw [Category.assoc, biprod.inr_snd, Category.comp_id] at h
  have hb := boundaryCycle (A := A) (-1)
  change (cycleFromUnit _ (complexSphereToDisk A (-1))).val = _ at hb
  exact h.trans hb

/-- 元の disk の収縮は、その同じ射影と包含で各斉次成分を回収する。 -/
lemma serreIntervalDiskContraction_apply (p q : ℤ) (hpq : p + -1 = q)
    (x : (serreInterval A).X p) :
    (serreIntervalDiskContraction A).v p q hpq x =
      (biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f q
        ((complexDiskContractingCochain A (-1)).v p q hpq
          ((biprod.snd : serreInterval A ⟶ complexDisk A (-1)).f p x)) := by
  rw [serreIntervalDiskContraction, cochain_comp_ofHom_apply, cochain_ofHom_comp_apply]

/-- 元の一端点への収縮は、元の零端点を元の辺に写す。 -/
lemma serreIntervalContraction_zero :
    (serreIntervalContraction A).v 0 (-1) (by omega)
      (cycleFromUnit _ (serreIntervalZero A)).val = serreIntervalEdge A := by
  simp only [serreIntervalContraction, Cochain.sub_v, ModuleCat.hom_sub,
    LinearMap.sub_apply, cochain_ofHom_comp_apply, serreIntervalDiskContraction_apply,
    serreIntervalZero_snd_value, map_zero, sub_zero]
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalAugmentation_zero A)
  change (serreIntervalAugmentation A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val =
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) at h
  rw [h]
  exact unitMinusOne_generator _ _

/-- 元の一端点への収縮は、同じ一端点を零に写す。 -/
lemma serreIntervalContraction_one :
    (serreIntervalContraction A).v 0 (-1) (by omega)
      (cycleFromUnit _ (serreIntervalOne A)).val = 0 := by
  simp only [serreIntervalContraction, Cochain.sub_v, ModuleCat.hom_sub,
    LinearMap.sub_apply, cochain_ofHom_comp_apply, serreIntervalDiskContraction_apply,
    serreIntervalOne_snd_value]
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalAugmentation_one A)
  change (serreIntervalAugmentation A).f 0 (cycleFromUnit _ (serreIntervalOne A)).val =
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) at h
  rw [h, unitMinusOne_generator]
  have hd := diskContraction_upper (A := A) (-1)
  change (complexDiskContractingCochain A (-1)).v 0 (-1) (by omega)
    ((complexDiskX₁ A (-1)).inv (1 : A)) = _ at hd
  rw [hd]
  change serreIntervalEdge A - serreIntervalEdge A = 0
  exact sub_self _

end SerrePositivity.KST.SConstruction
