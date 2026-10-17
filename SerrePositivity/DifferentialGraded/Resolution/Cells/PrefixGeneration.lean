module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorAppend
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Prefix

/-! # 元のHomと生成元の合成から前方path追加を復元する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma generator_internalComposition_inclusion (i : I) (w : List I) (y : D) :
    ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y) ≫
      (C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
        C.internalComposition A D I (C.source i) (C.target i) y =
    (C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
      C.appendMap A D I [i] w (C.source i) (C.target i) y ≫
        C.inclusion A D I (i :: w) (C.source i) y := by
  rw [generatorInclusion, comp_whiskerRight, Category.assoc, whisker_exchange_assoc,
    ← tensorHom_def'_assoc, internalComposition_inclusion]
  rfl

lemma prefixPath_generated (i : I) (x y : D) :
    (homObject A D x (C.source i)) ◁
      ((C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
        C.internalComposition A D I (C.source i) (C.target i) y) ≫
      C.internalPrepend A D I x (C.source i) y = C.prefixPath A D I i x y := by
  apply (C.prefixCofanIsColimit A D I i x y).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫
      (homObject A D x (C.source i)) ◁
        ((C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
          C.internalComposition A D I (C.source i) (C.target i) y) ≫
        C.internalPrepend A D I x (C.source i) y =
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫ C.prefixPath A D I i x y
  rw [prefixPath_inclusion, ← whiskerLeft_comp_assoc, generator_internalComposition_inclusion]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [internalPrepend_inclusion]
  have h := congrArg (fun f => f ≫ C.inclusion A D I (i :: w) x y)
    (C.prependMap_generatorTerm_append A D I i w x y)
  simpa only [term_cons, whiskerLeft_comp, Category.assoc, Category.id_comp] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
