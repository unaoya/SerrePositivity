module

public import SerrePositivity.EInfinity.PowerOperation.MayClosedHomology

/-!
# 同じホモロジー類を表す sphere 射のホモトピー

May, Proposition 2.3 の代表元独立性の補助。
二つの閉元の差が境界なら、二つの sphere 射の差は可縮な disk を経由する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory Limits HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
variable {k : Type u} [CommRing k]

lemma maySphereHomEquiv_sub (K : Complex k) (i : ℤ)
    (f g : complexSphere k i ⟶ K) :
    (complexSphereHomEquiv k K i (f - g)).val =
      (complexSphereHomEquiv k K i f).val - (complexSphereHomEquiv k K i g).val := by
  change ((singleObjXSelf (.up ℤ) i (𝟙_ (ModuleCat k))).inv ≫ (f - g).f i) (1 : k) = _
  rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub]
  rfl

/-- sphere の単位生成元を代表射で評価すると、指定した閉元を回収する。 -/
lemma maySphereGenerator_map (K : Complex k) (i : ℤ) (a : MayClosed K i) :
    mayClosedMap ((complexSphereHomEquiv k K i).symm a) i
      (complexSphereHomEquiv k (complexSphere k i) i (𝟙 _)) = a := by
  apply Subtype.ext
  have h : (complexSphereHomEquiv k K i
      (𝟙 _ ≫ (complexSphereHomEquiv k K i).symm a)).val =
      (((complexSphereHomEquiv k K i).symm a).f i)
        (complexSphereHomEquiv k (complexSphere k i) i (𝟙 _)).val := by
    change ((singleObjXSelf (.up ℤ) i (𝟙_ (ModuleCat k))).inv ≫
      (𝟙 _ ≫ (complexSphereHomEquiv k K i).symm a).f i) (1 : k) = _
    rw [HomologicalComplex.comp_f]
    rfl
  rw [Category.id_comp] at h
  exact h.symm.trans (congrArg Subtype.val ((complexSphereHomEquiv k K i).apply_symm_apply a))

/-- 同じ実ホモロジー類を表す二閉元の sphere 射は鎖ホモトピック。 -/
lemma maySphereHomotopy_exists (K : Complex k) (i : ℤ) (a b : MayClosed K i)
    (hab : mayClosedClass K i a = mayClosedClass K i b) :
    Nonempty (Homotopy ((complexSphereHomEquiv k K i).symm a)
      ((complexSphereHomEquiv k K i).symm b)) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, j + 1 = i := ⟨i - 1, by omega⟩
  have hz : mayClosedClass K (j + 1) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have he := (mayClosedClass_eq_zero_iff K (j + 1) (a - b)).mp hz
  rw [show j + 1 - 1 = j by omega] at he
  obtain ⟨c, hc⟩ := he
  let f := (complexSphereHomEquiv k K (j + 1)).symm a
  let g := (complexSphereHomEquiv k K (j + 1)).symm b
  let d := (complexDiskHomEquiv k K j).symm c
  have hfg : f - g = complexSphereToDisk k j ≫ d := by
    apply (complexSphereHomEquiv k K (j + 1)).injective
    apply Subtype.ext
    rw [maySphereHomEquiv_sub, complexSphereToDisk_comp]
    change (complexSphereHomEquiv k K (j + 1) ((complexSphereHomEquiv k K (j + 1)).symm a)).val -
      (complexSphereHomEquiv k K (j + 1) ((complexSphereHomEquiv k K (j + 1)).symm b)).val = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change a.val - b.val = K.d j (j + 1)
      (complexDiskHomEquiv k K j ((complexDiskHomEquiv k K j).symm c))
    rw [Equiv.apply_symm_apply]
    exact hc.symm
  have H := ((complexDiskContractingHomotopy k j).compLeft (complexSphereToDisk k j)).compRight d
  have H' : Homotopy (f - g) 0 := by
    rw [hfg]
    simpa only [Category.comp_id, comp_zero, zero_comp] using H
  have H'' := H'.add (Homotopy.refl g)
  exact ⟨by simpa only [sub_add_cancel, zero_add] using H''⟩

/-- 同じホモロジー類の二つの sphere 射の指定鎖ホモトピー。 -/
def maySphereHomotopy (K : Complex k) (i : ℤ) (a b : MayClosed K i)
    (hab : mayClosedClass K i a = mayClosedClass K i b) :
    Homotopy ((complexSphereHomEquiv k K i).symm a)
      ((complexSphereHomEquiv k K i).symm b) :=
  Classical.choice (maySphereHomotopy_exists K i a b hab)

end SerrePositivity.EInfinity.PowerOperation
