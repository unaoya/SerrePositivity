module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightNaturality
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftNaturality
public import SerrePositivity.DifferentialGraded.Module.HomWhisker

/-! # 結合比較の右加群同型と左作用の全Hom自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

@[simp]
lemma associatorRightModuleIso_hom_component (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    moduleMorphismComponent A B
      ((compose A B E F (compose A B C E P Q) R).rightAt f)
      ((compose A B C F P (compose A C E F Q R)).rightAt f)
      (associatorRightModuleIso A B C E F P Q R f).hom b =
      (associatorValueIso A B C E F P Q R b f).hom :=
  associatorRightModuleIso_hom_eval A B C E F P Q R b f

/-- 左F作用に関する自然性は値のHomだけでなく右B加群の主Hom endで成り立つ。 -/
lemma associatorRightModuleIso_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f f' : F) :
    (compose A B E F (compose A B C E P Q) R).toFunctor.map f f' ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f')
        ((compose A B C F P (compose A C E F Q R)).rightAt f')
        (associatorRightModuleIso A B C E F P Q R f').hom =
    (compose A B C F P (compose A C E F Q R)).toFunctor.map f f' ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f')
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [associatorRightModuleIso_hom_component]
  have h := associatorValue_left_naturality A B C E F P Q R b f f'
  unfold associatorLeftMap associatorRightMap at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
