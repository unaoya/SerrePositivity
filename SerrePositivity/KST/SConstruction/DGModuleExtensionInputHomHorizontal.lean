module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomWhiskering
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomComposition
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalComposition

/-! # 元の実加群延長と入力 Hom end の横合成
概要：二つの元の高次入力作用は、実合成比較の共役後に元の入力横合成を回収する。
方針：前後合成の全 Hom 式を使い、中間の比較同型を相殺して入力の縦合成へ戻す。
規約：元の入力 Hom・実加群・合成比較を保持する。使われ方：Perf の高次入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 元の入力 Hom end の横合成は、同じ実加群合成比較の共役で厳密に回収される。 -/
lemma dgModuleExtensionInputHom_horizontal (F F' : DGFunctor A D E)
    (G G' : DGFunctor A E T) (M : RightModule A D) :
    ((dgModuleExtensionInputHom A D E F F' M ≫ (dgModuleExtension A E T G).map
          ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F').obj M)) ⊗ₘ
        dgModuleExtensionInputHom A E T G G' ((dgModuleExtension A D E F').obj M)) ≫
        moduleComposition A T _ _ _ ≫
          enrichedClosedIsoConjugation (Complex A) (dgModuleExtensionCompositionAt A D E T F G M)
            (dgModuleExtensionCompositionAt A D E T F' G' M) =
      dgFunctorHorizontal A D E T F F' G G' ≫
        dgModuleExtensionInputHom A D T (F.comp G) (F'.comp G') M := by
  have hc := congrArg (fun k =>
    ((dgModuleExtensionInputHom A D E F F' M ≫ (dgModuleExtension A E T G).map
        ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F').obj M)) ⊗ₘ
      dgModuleExtensionInputHom A E T G G' ((dgModuleExtension A D E F').obj M)) ≫ k)
    (enrichedClosedIsoConjugation_comp (Complex A)
      (dgModuleExtensionCompositionAt A D E T F G M)
      (dgModuleExtensionCompositionAt A D E T F' G M)
      (dgModuleExtensionCompositionAt A D E T F' G' M))
  simp only [tensorHom_comp_tensorHom_assoc] at hc
  rw [dgModuleExtensionInputHom_post, dgModuleExtensionInputHom_pre] at hc
  have hi := congrArg (fun k =>
    (dgFunctorHomPost A D E T G F F' ⊗ₘ dgFunctorHomPre A E T D F' G G') ≫ k)
    (dgModuleExtensionInputHom_composition A D T (F.comp G) (F'.comp G) (F'.comp G') M)
  simp only [tensorHom_comp_tensorHom_assoc] at hi
  simp only [dgFunctorHorizontal, Category.assoc]
  convert hc.symm.trans hi.symm using 1
  rfl

end SerrePositivity.KST.SConstruction
