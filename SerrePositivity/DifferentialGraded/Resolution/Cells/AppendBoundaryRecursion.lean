module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundaryHead
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendLiftCochain
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrefixBoundary
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainPrecomp

/-! # 非空の左pathの連結後の境界置換の再帰式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)


lemma appendRight_cons_factor (b : I) (w : List I) (x y z : D) :
    C.appendRight A D I (b :: w) x y z =
    (((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.internalHom A D I y z)).hom) ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)) ≫
      C.prefixPath A D I b x z := by
  rw [appendRight_cons]
  simp only [whiskerLeft_comp, Category.assoc]

lemma appendRight_replaceFirst_factored (b : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.internalHom A D I y z)).hom) ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z))).comp
      (C.internalReplaceFirst A D I b x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) (C.term A D I (b :: w) x y)
      (C.term A D I w x y)).f 1
      (C.replaceFirst A D I b w x y)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) := by
  simpa only [whiskerLeft_comp, Category.assoc] using C.appendRight_replaceFirst A D I b w x y z

lemma appendRight_replacement_cons (b : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (C.appendRight A D I (b :: w) x y z)).comp
      (C.replacement A D I x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) (C.term A D I (b :: w) x y)
      (C.term A D I w x y)).f 1
      (C.replaceFirst A D I b w x y)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) +
    C.appendLiftCochain A D I b w x y z 1
      ((Cochain.ofHom (C.appendRight A D I w (C.target b) y z)).comp
        (C.replacement A D I (C.target b) z) (zero_add 1)) := by
  have hc := C.appendRight_cons_factor A D I b w x y z
  have hh := C.appendRight_replaceFirst_factored A D I b w x y z
  rw [hc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    prefixPath_replacement, Cochain.comp_add _ _ _ (zero_add 1), hh]
  apply congrArg₂ (· + ·) rfl
  have ht := prefixTensor_cochain_precomp (homObject A D x (C.source b))
    (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)
    (C.internalHom A D I (C.target b) z) (C.internalHom A D I (C.target b) z)
    (C.internalHom A D I x z) 1 (C.appendRight A D I w (C.target b) y z)
    (C.replacement A D I (C.target b) z) (C.prefixPath A D I b x z)
  change _ = C.appendLiftCochain A D I b w x y z 1 _
  unfold appendLiftCochain
  simp only [term_cons, Category.assoc] at ht ⊢
  with_reducible exact ht

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
