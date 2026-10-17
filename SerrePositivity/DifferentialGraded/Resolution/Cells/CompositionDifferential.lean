module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionBoundary
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Differential
public import SerrePositivity.DifferentialGraded.Complexes.Composition

/-! # 任意次数cellの全合成の微分整合性：CompositionDifferential -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 全消去Leibniz則の斉次成分。右の消去項の符号は左の次数p。 -/
lemma internalComposition_replacement_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (C.internalHom A D I x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.replacement A D I x z).v n (n + 1) rfl
      ((C.internalComposition A D I x y z).f n
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((C.replacement A D I x y).v p (p + 1) rfl a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.replacement A D I y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (C.internalHom A D I x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (C.internalComposition_replacement A D I x y z)
  simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply] at h
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, cochain_comp_ofHom_apply,
    tensorRightHom_apply, tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

/-- 最終Homの全微分についてのLeibniz則。 -/
lemma internalComposition_total_d_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (C.internalHom A D I x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.attachedHom A D I x z).d n (n + 1)
      ((C.internalComposition A D I x y z).f n
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((C.attachedHom A D I x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.attachedHom A D I y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((C.internalComposition A D I x y z).comm n (n + 1))
    (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))
  change (C.internalHom A D I x z).d n (n + 1) (_ : (C.internalHom A D I x z).X n) =
    (C.internalComposition A D I x y z).f (n + 1)
      ((C.internalHom A D I x y ⊗ C.internalHom A D I y z).d n (n + 1)
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (C.internalHom A D I x y ⊗ C.internalHom A D I y z).X (n + 1) =>
    (C.internalComposition A D I x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [attachedHom_d, attachedHom_d, attachedHom_d]
  change (C.internalHom A D I x z).d n (n + 1)
      ((C.internalComposition A D I x y z).f n
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) +
      (C.replacement A D I x z).v n (n + 1) rfl
        ((C.internalComposition A D I x y z).f n
          (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) (((C.internalHom A D I x y).d p (p + 1) a +
          (C.replacement A D I x y).v p (p + 1) rfl a) ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((C.internalHom A D I y z).d q (q + 1) b +
          (C.replacement A D I y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi
    (C.internalComposition_replacement_apply A D I x y z p q n hn a b)).trans (by
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 全pathの最終Hom複体間の合成。最終微分に関する実際のchain map。 -/
def attachedComposition (x y z : D) :
    C.attachedHom A D I x y ⊗ C.attachedHom A D I y z ⟶ C.attachedHom A D I x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) i j n h ≫
      (C.internalComposition A D I x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact C.internalComposition_total_d_apply A D I x y z i j (i + j) rfl a b)

lemma attachedComposition_ι (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) i j n hn ≫
      (C.attachedComposition A D I x y z).f n =
    ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) i j n hn ≫
      (C.internalComposition A D I x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
