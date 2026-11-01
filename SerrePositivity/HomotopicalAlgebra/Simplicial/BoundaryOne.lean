module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! # The actual boundary of the interval is a binary coproduct of vertices -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.BoundaryOne

lemma square : SSet.Subcomplex.BicartSq.{v} ⊥ (SSet.stdSimplex.face {0})
    (SSet.stdSimplex.face {1}) (SSet.boundary 1) where
  sup_eq := by
    have h₀ : SSet.stdSimplex.face.{v} {0} ≤ SSet.boundary 1 := by
      convert SSet.face_singleton_compl_le_boundary (1 : Fin 2) using 1
      congr 1
    have h₁ : SSet.stdSimplex.face.{v} {1} ≤ SSet.boundary 1 := by
      convert SSet.face_singleton_compl_le_boundary (0 : Fin 2) using 1
      congr 1
    apply le_antisymm (sup_le h₀ h₁)
    rw [SSet.boundary_eq_iSup, iSup_le_iff]
    intro i
    fin_cases i
    · convert (le_sup_right : SSet.stdSimplex.face.{v} {1} ≤
        SSet.stdSimplex.face {0} ⊔ SSet.stdSimplex.face {1}) using 1
      congr 1
    · convert (le_sup_left : SSet.stdSimplex.face.{v} {0} ≤
        SSet.stdSimplex.face {0} ⊔ SSet.stdSimplex.face {1}) using 1
      congr 1
  inf_eq := by
    rw [SSet.stdSimplex.face_inter_face,
      show ({0} ⊓ {1} : Finset (Fin 2)) = ∅ by decide, SSet.stdSimplex.face_empty]

lemma zero_comp :
    (SSet.stdSimplex.faceSingletonIso.{v} (0 : Fin 2)).hom ≫
      SSet.Subcomplex.homOfLE square.le₂₄ = SSet.boundary.ι (1 : Fin 2) := by
  apply (cancel_mono (SSet.boundary.{v} 1).ι).mp
  rw [Category.assoc]
  exact SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ.trans
    (SSet.boundary.ι_ι (1 : Fin 2)).symm

lemma one_comp :
    (SSet.stdSimplex.faceSingletonIso.{v} (1 : Fin 2)).hom ≫
      SSet.Subcomplex.homOfLE square.le₃₄ = SSet.boundary.ι (0 : Fin 2) := by
  apply (cancel_mono (SSet.boundary.{v} 1).ι).mp
  rw [Category.assoc]
  exact SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ.trans
    (SSet.boundary.ι_ι (0 : Fin 2)).symm

def faceCofanIsColimit : IsColimit (BinaryCofan.mk
    (SSet.Subcomplex.homOfLE square.{v}.le₂₄) (SSet.Subcomplex.homOfLE square.le₃₄)) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ square.isPushout.desc f g (SSet.Subcomplex.isInitialBot.hom_ext _ _))
    (fun f g ↦ square.isPushout.inl_desc f g _)
    (fun f g ↦ square.isPushout.inr_desc f g _)
    (fun f g _ hf hg ↦ square.isPushout.hom_ext
      (hf.trans (square.isPushout.inl_desc f g _).symm)
      (hg.trans (square.isPushout.inr_desc f g _).symm))

def isColimit : IsColimit (BinaryCofan.mk
    (SSet.boundary.ι.{v} (1 : Fin 2)) (SSet.boundary.ι (0 : Fin 2))) := by
  have h := BinaryCofan.isColimitCompLeftIso _
    (SSet.stdSimplex.faceSingletonIso.{v} (0 : Fin 2)).hom faceCofanIsColimit
  have h' := BinaryCofan.isColimitCompRightIso _
    (SSet.stdSimplex.faceSingletonIso.{v} (1 : Fin 2)).hom h
  change IsColimit (BinaryCofan.mk
    ((SSet.stdSimplex.faceSingletonIso.{v} (0 : Fin 2)).hom ≫
      SSet.Subcomplex.homOfLE square.le₂₄)
    ((SSet.stdSimplex.faceSingletonIso.{v} (1 : Fin 2)).hom ≫
      SSet.Subcomplex.homOfLE square.le₃₄)) at h'
  rw [zero_comp, one_comp] at h'
  exact h'

end SerrePositivity.HomotopyFunctionComplex.BoundaryOne
