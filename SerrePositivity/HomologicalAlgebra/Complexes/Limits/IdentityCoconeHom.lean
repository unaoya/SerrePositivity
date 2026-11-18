module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveHomotopyInverse
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# 恒等 mapping cocone への射の実 cochain 表示

概要：恒等 mapping cocone への射は元の −1-cochain で一意に決まる。
方針：指定した射影の零ホモトピーと実二射影の分解を使う。
規約：元の射影・符号・全次数を保持する。
使われ方：次数別の線形射を表現する可縮 disk の全 Hom 同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma identityCoconeSnd_boundary (K : Complex A) :
    δ (-1) 0 (mappingCocone.snd (𝟙 K)) = -Cochain.ofHom (mappingCocone.fst (𝟙 K)) := by
  have h := δ_ofHomotopy (_root_.SerrePositivity.ProjectiveHomotopyInverse.coconeIdentityProjectionNullhomotopy K)
  have hc : Cochain.ofHomotopy (_root_.SerrePositivity.ProjectiveHomotopyInverse.coconeIdentityProjectionNullhomotopy K) =
      -(mappingCocone.snd (𝟙 K)) := by
    change (Cochain.equivHomotopy _ _ (_root_.SerrePositivity.ProjectiveHomotopyInverse.coconeIdentityProjectionNullhomotopy K)).1 = _
    rw [_root_.SerrePositivity.ProjectiveHomotopyInverse.coconeIdentityProjectionNullhomotopy, Equiv.apply_symm_apply]
  rw [hc] at h
  rw [δ_neg, Cochain.ofHom_zero, sub_zero] at h
  exact neg_eq_iff_eq_neg.mp h
lemma identityCocone_hom_ext {P K : Complex A} (f g : P ⟶ mappingCocone (𝟙 K))
    (h : (Cochain.ofHom f).comp (mappingCocone.snd (𝟙 K)) (zero_add (-1)) =
      (Cochain.ofHom g).comp (mappingCocone.snd (𝟙 K)) (zero_add (-1))) : f = g := by
  have hδ := congrArg (δ (-1) 0) h
  simp only [δ_comp _ _ (zero_add (-1)) 1 0 0 (by simp) (by simp) (by simp),
    δ_ofHom, Cochain.zero_comp, smul_zero,
    _root_.SerrePositivity.ComplexLimits.identityCoconeSnd_boundary, Cochain.comp_neg, ← Cochain.ofHom_comp, add_zero, neg_inj] at hδ
  have hf : f ≫ mappingCocone.fst (𝟙 K) = g ≫ mappingCocone.fst (𝟙 K) := by
    exact Cochain.ofHom_injective hδ
  apply HomologicalComplex.Hom.ext
  funext p
  have hv := Cochain.congr_v h p (p - 1) (by omega)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at hv
  have hfv := congrArg (fun k => k.f p) hf
  simp only [HomologicalComplex.comp_f] at hfv
  calc
    f.f p = f.f p ≫ 𝟙 _ := by simp
    _ = f.f p ≫ ((mappingCocone.fst (𝟙 K)).f p ≫
      (mappingCocone.inl (𝟙 K)).v p p (add_zero p) +
        (mappingCocone.snd (𝟙 K)).v p (p - 1) (by omega) ≫
          (mappingCocone.inr (𝟙 K)).1.v (p - 1) p (by omega)) :=
      congrArg (fun z => f.f p ≫ z) (mappingCocone.id_X (𝟙 K) p (p - 1) (by omega)).symm
    _ = g.f p ≫ 𝟙 _ := by
      rw [Preadditive.comp_add, ← Category.assoc, hfv, Category.assoc,
        ← Category.assoc (f.f p) ((mappingCocone.snd (𝟙 K)).v p (p - 1) (by omega)), hv,
        Category.assoc,
        ← Preadditive.comp_add, mappingCocone.id_X]
    _ = g.f p := by simp

def identityCoconeHomEquiv (P K : Complex A) :
    (P ⟶ mappingCocone (𝟙 K)) ≃ Cochain P K (-1) where
  toFun f := (Cochain.ofHom f).comp (mappingCocone.snd (𝟙 K)) (zero_add (-1))
  invFun β := (mappingCocone.liftCocycle (𝟙 K)
    (Cocycle.mk (-δ (-1) 0 β) 1 (by simp) (by simp [δ_neg, δ_δ])) β
      (by simp) (by simp)).homOf
  left_inv f := by
    apply _root_.SerrePositivity.ComplexLimits.identityCocone_hom_ext
    simp only [Cocycle.cochain_ofHom_homOf_eq_coe, mappingCocone.liftCocycle_coe,
      mappingCocone.liftCochain_comp_snd]
  right_inv β := by
    simp only [Cocycle.cochain_ofHom_homOf_eq_coe, mappingCocone.liftCocycle_coe,
      mappingCocone.liftCochain_comp_snd]

end SerrePositivity.ComplexLimits
