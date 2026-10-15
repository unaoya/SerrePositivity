module
public import SerrePositivity.DifferentialGraded.Complexes.ConeMaps

/-! # 包含と等しい射を用いるMathlibのcone回転比較

加群射の評価は包含と命題的に等しいため、その等式を明示的な引数にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

def complexConeRotationHom (f : K ⟶ L) (ψ : L ⟶ mappingCone f) (hψ : ψ = mappingCone.inr f) :
    K⟦(1 : ℤ)⟧ ⟶ mappingCone ψ := by
  subst ψ
  exact (mappingCone.rotateHomotopyEquiv f).hom

def complexConeRotationInv (f : K ⟶ L) (ψ : L ⟶ mappingCone f) (hψ : ψ = mappingCone.inr f) :
    mappingCone ψ ⟶ K⟦(1 : ℤ)⟧ := by
  subst ψ
  exact (mappingCone.rotateHomotopyEquiv f).inv

lemma complexConeRotationHom_cochain (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    Cochain.ofHom (complexConeRotationHom f ψ hψ) =
      mappingCone.liftCochain ψ (-(Cochain.ofHom f).leftShift 1 1 (zero_add 1))
        (-(mappingCone.inl f).leftShift 1 0 (neg_add_cancel 1)) (zero_add 1) := by
  subst ψ
  simp only [complexConeRotationHom, mappingCone.rotateHomotopyEquiv, mappingCone.ofHom_lift,
    Cocycle.coe_neg, Cocycle.leftShift_coe, Cocycle.ofHom_coe]

lemma complexConeRotationInv_cochain (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    Cochain.ofHom (complexConeRotationInv f ψ hψ) =
      mappingCone.descCochain ψ 0 (Cochain.ofHom (mappingCone.triangle f).mor₃)
        (neg_add_cancel 1) := by
  subst ψ
  simp only [complexConeRotationInv, mappingCone.rotateHomotopyEquiv, mappingCone.ofHom_desc]

lemma complexConeRotation_hom_inv (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    complexConeRotationHom f ψ hψ ≫ complexConeRotationInv f ψ hψ = 𝟙 _ := by
  subst ψ
  apply HomologicalComplex.Hom.ext
  funext n
  let H := (mappingCone.rotateHomotopyEquiv f).homotopyHomInvId
  have hzero (i j : ℤ) : H.hom i j = 0 := rfl
  have hc := H.comm n
  have hdn : dNext (C := K⟦(1 : ℤ)⟧) (D := K⟦(1 : ℤ)⟧) n H.hom = 0 := by
    change _ ≫ H.hom ((ComplexShape.up ℤ).next n) n = 0
    rw [hzero, comp_zero]
  have hpd : prevD (C := K⟦(1 : ℤ)⟧) (D := K⟦(1 : ℤ)⟧) n H.hom = 0 := by
    change H.hom n ((ComplexShape.up ℤ).prev n) ≫ _ = 0
    rw [hzero, zero_comp]
  rw [hdn, hpd, zero_add, zero_add] at hc
  exact hc

lemma complexConeRotation_inv_hom_boundary (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    δ (-1) 0 (-(mappingCone.snd ψ).comp
      ((mappingCone.snd f).comp (mappingCone.inl ψ) (zero_add (-1))) (zero_add (-1))) =
      Cochain.ofHom (complexConeRotationInv f ψ hψ ≫ complexConeRotationHom f ψ hψ) -
        Cochain.ofHom (𝟙 (mappingCone ψ)) := by
  subst ψ
  let H := (mappingCone.rotateHomotopyEquiv f).homotopyInvHomId
  have hc : ((Cochain.equivHomotopy _ _) H).val =
      -(mappingCone.snd (mappingCone.inr f)).comp
        ((mappingCone.snd f).comp (mappingCone.inl (mappingCone.inr f)) (zero_add (-1)))
        (zero_add (-1)) := by
    simp only [H, mappingCone.rotateHomotopyEquiv, Equiv.apply_symm_apply]
  have hd := ((Cochain.equivHomotopy _ _) H).property
  rw [hc] at hd
  exact (eq_sub_iff_add_eq).2 hd.symm

lemma complexConeRotation_connecting_boundary (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    δ (-1) 0 (-(mappingCone.snd f).comp (mappingCone.inl ψ) (zero_add (-1))) =
      (show Cochain (mappingCone f) (mappingCone ψ) 0 from
        Cochain.ofHom ((mappingCone.triangle f).mor₃ ≫ complexConeRotationHom f ψ hψ)) -
          Cochain.ofHom (mappingCone.inr ψ) := by
  subst ψ
  let H := mappingCone.rotateHomotopyEquivComm₂Homotopy f
  have hc : ((Cochain.equivHomotopy _ _) H).val =
      -(mappingCone.snd f).comp (mappingCone.inl (mappingCone.inr f)) (zero_add (-1)) := by
    simp only [H, mappingCone.rotateHomotopyEquivComm₂Homotopy, Equiv.apply_symm_apply]
  have hd := ((Cochain.equivHomotopy _ _) H).property
  rw [hc] at hd
  exact (eq_sub_iff_add_eq).2 hd.symm

lemma complexConeRotation_connecting (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    complexConeRotationHom f ψ hψ ≫ (mappingCone.triangle ψ).mor₃ = -f⟦(1 : ℤ)⟧' := by
  subst ψ
  exact mappingCone.rotateHomotopyEquiv_comm₃ f

end SerrePositivity.DifferentialGraded
